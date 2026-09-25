module Elm.TypeInference.Unify exposing (TypeAlias, UnifyConfig, unifyMany)

import Dict exposing (Dict)
import Dict.Extra
import Elm.Syntax.FullModuleName as FullModuleName exposing (FullModuleName)
import Elm.TypeInference.Error exposing (Error, ErrorDetails(..))
import Elm.TypeInference.ModuleIds as ModuleIds exposing (ModuleId)
import Elm.TypeInference.State as State exposing (StateM)
import Elm.TypeInference.SubstitutionMap as SubstitutionMap
import Elm.TypeInference.Type exposing (PackageName, VarName)
import Elm.TypeInference.Type.Internal as TypeI exposing (MonoType(..))
import Elm.TypeInference.TypeVar as TypeVar
    exposing
        ( SuperType(..)
        , TypeVar
        , TypeVarStyle(..)
        )
import List.ExtraExtra


type alias TypeAlias =
    { type_ : MonoType
    , args : List TypeVar
    }


type alias TypeAliases =
    Dict ( ModuleId, PackageName, VarName ) TypeAlias


type alias UnifyConfig =
    { typeAliases : TypeAliases
    , moduleName : FullModuleName
    , declarationNames : List VarName
    , moduleMapping : ModuleIds.Mapping
    }


unifyMany : UnifyConfig -> List ( MonoType, MonoType ) -> StateM ()
unifyMany cfg eqs =
    \state -> unifyManyHelp cfg eqs state


{-| Intentionally not a State.foldl to reduce GC pressure.
-}
unifyManyHelp : UnifyConfig -> List ( MonoType, MonoType ) -> State.State -> ( Result Error (), State.State )
unifyManyHelp cfg eqs state =
    case eqs of
        [] ->
            ( State.okUnit, state )

        ( t1, t2 ) :: rest ->
            let
                ( st1, _, subst1 ) =
                    SubstitutionMap.substituteMono state.subst t1

                ( st2, _, subst2 ) =
                    SubstitutionMap.substituteMono subst1 t2

                state1 : State.State
                state1 =
                    { nextId = state.nextId
                    , nodeIds = state.nodeIds
                    , lexicalEnv = state.lexicalEnv
                    , globalEnv = state.globalEnv
                    , subst = subst2
                    , letRank = state.letRank
                    }
            in
            case
                unifyMono
                    cfg
                    st1
                    st2
                    state1
            of
                ( Err err, newState ) ->
                    ( Err err, newState )

                ( Ok (), newState ) ->
                    unifyManyHelp cfg rest newState


{-| Pair the two record field dicts up _by name_.
`Nothing` if the key sets differ at all.
-}
zipRecordFields : Dict VarName MonoType -> Dict VarName MonoType -> Maybe (List ( MonoType, MonoType ))
zipRecordFields bindings1 bindings2 =
    Dict.merge
        (\_ _ _ -> Nothing)
        (\_ v1 v2 acc -> Maybe.map (\eqs -> ( v1, v2 ) :: eqs) acc)
        (\_ _ _ -> Nothing)
        bindings1
        bindings2
        (Just [])


typeMismatch : UnifyConfig -> MonoType -> MonoType -> StateM ()
typeMismatch cfg t1 t2 =
    let
        ( pubT1, pubT2 ) =
            TypeI.normalizeAndToPublicPair cfg.moduleMapping
                (TypeI.expandAliasDeep cfg.typeAliases t1)
                (TypeI.expandAliasDeep cfg.typeAliases t2)
    in
    State.error
        { moduleName = FullModuleName.toModuleName cfg.moduleName
        , declarationNames = cfg.declarationNames
        , details = TypeMismatch pubT1 pubT2
        }


recordBindings : UnifyConfig -> MonoType -> MonoType -> Dict VarName MonoType -> Dict VarName MonoType -> StateM ()
recordBindings cfg t1 t2 bindings1 bindings2 =
    case zipRecordFields bindings1 bindings2 of
        Nothing ->
            typeMismatch cfg t1 t2

        Just eqs ->
            unifyMany cfg eqs


unifyRecordVsExtensible :
    UnifyConfig
    -> MonoType
    -> MonoType
    -> Dict VarName MonoType
    ->
        { extensionTypevar : MonoType
        , fields : Dict VarName MonoType
        }
    -> StateM ()
unifyRecordVsExtensible cfg t1 t2 recordFields er =
    case er.extensionTypevar of
        Record extFields ->
            let
                overlapEqs : List ( MonoType, MonoType )
                overlapEqs =
                    Dict.merge
                        (\_ _ eqs -> eqs)
                        (\_ v1 v2 eqs -> ( v1, v2 ) :: eqs)
                        (\_ _ eqs -> eqs)
                        extFields
                        er.fields
                        []

                combined : Dict VarName MonoType
                combined =
                    Dict.union er.fields extFields
            in
            State.do (unifyMany cfg overlapEqs) <| \() ->
            recordBindings cfg t1 t2 combined recordFields

        ExtensibleRecord extEr ->
            let
                overlapEqs : List ( MonoType, MonoType )
                overlapEqs =
                    Dict.merge
                        (\_ _ eqs -> eqs)
                        (\_ v1 v2 eqs -> ( v1, v2 ) :: eqs)
                        (\_ _ eqs -> eqs)
                        extEr.fields
                        er.fields
                        []

                merged : Dict VarName MonoType
                merged =
                    Dict.union er.fields extEr.fields
            in
            State.do (unifyMany cfg overlapEqs) <| \() ->
            unifyRecordVsExtensible cfg
                t1
                t2
                recordFields
                { extensionTypevar = extEr.extensionTypevar
                , fields = merged
                }

        _ ->
            let
                ( residual, matchedEqs, matchedCount ) =
                    Dict.foldl
                        (\k v ( res, eqs, n ) ->
                            case Dict.get k er.fields of
                                Just ev ->
                                    ( res
                                    , ( v, ev ) :: eqs
                                    , n + 1
                                    )

                                Nothing ->
                                    ( Dict.insert k v res
                                    , eqs
                                    , n
                                    )
                        )
                        ( Dict.empty, [], 0 )
                        recordFields
            in
            -- matchedCount /= Dict.size er.fields
            if matchedCount - Dict.size er.fields /= 0 then
                typeMismatch cfg t1 t2

            else
                unifyMany cfg
                    (( er.extensionTypevar, Record residual )
                        :: matchedEqs
                    )


unifyMono : UnifyConfig -> MonoType -> MonoType -> StateM ()
unifyMono cfg t1 t2 =
    case t1 of
        TypeVar v ->
            bind cfg v t2

        Int ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Int ->
                    -- no substitution needed
                    State.pureUnit

                _ ->
                    typeMismatch cfg t1 t2

        Float ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Float ->
                    -- no substitution needed
                    State.pureUnit

                _ ->
                    typeMismatch cfg t1 t2

        String ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                String ->
                    -- no substitution needed
                    State.pureUnit

                _ ->
                    typeMismatch cfg t1 t2

        Char ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Char ->
                    -- no substitution needed
                    State.pureUnit

                _ ->
                    typeMismatch cfg t1 t2

        Bool ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Bool ->
                    -- no substitution needed
                    State.pureUnit

                _ ->
                    typeMismatch cfg t1 t2

        Unit ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Unit ->
                    -- no substitution needed
                    State.pureUnit

                _ ->
                    typeMismatch cfg t1 t2

        Function a ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Function b ->
                    unifyMany
                        cfg
                        [ ( a.from, b.from )
                        , ( a.to, b.to )
                        ]

                _ ->
                    typeMismatch cfg t1 t2

        List list1 ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                List list2 ->
                    unifyMono cfg list1 list2

                _ ->
                    typeMismatch cfg t1 t2

        Tuple2 t1e1 t1e2 ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Tuple2 t2e1 t2e2 ->
                    unifyMany
                        cfg
                        [ ( t1e1, t2e1 )
                        , ( t1e2, t2e2 )
                        ]

                _ ->
                    typeMismatch cfg t1 t2

        Tuple3 t1e1 t1e2 t1e3 ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Tuple3 t2e1 t2e2 t2e3 ->
                    unifyMany
                        cfg
                        [ ( t1e1, t2e1 )
                        , ( t1e2, t2e2 )
                        , ( t1e3, t2e3 )
                        ]

                _ ->
                    typeMismatch cfg t1 t2

        Record r1Fields ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                Record r2Fields ->
                    recordBindings cfg t1 t2 r1Fields r2Fields

                ExtensibleRecord r2 ->
                    unifyRecordVsExtensible cfg t1 t2 r1Fields r2

                _ ->
                    typeMismatch cfg t1 t2

        ExtensibleRecord r1 ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                ExtensibleRecord r2 ->
                    {- Fields that only one side mentions must be added to the other
                       side's required fields.
                       Both sides' extension typevars (the r in { r | ... })
                       now need to be the same var.

                       ie.
                       - getX : { row1 | x : Float } -> Float
                       - getY : { row2 | y : Float } -> Float
                       - sum r = getX r + getY r
                       Use them both on the same record and you get
                       - sum : { commonVar | x : Float, y : Float } -> Float
                    -}
                    let
                        ( onlyIn1, onlyIn2, sharedEqs ) =
                            Dict.merge
                                (\k v ( o1, o2, eqs ) ->
                                    ( Dict.insert k v o1
                                    , o2
                                    , eqs
                                    )
                                )
                                (\_ v1 v2 ( o1, o2, eqs ) ->
                                    ( o1
                                    , o2
                                    , ( v1, v2 ) :: eqs
                                    )
                                )
                                (\k v ( o1, o2, eqs ) ->
                                    ( o1
                                    , Dict.insert k v o2
                                    , eqs
                                    )
                                )
                                r1.fields
                                r2.fields
                                ( Dict.empty, Dict.empty, [] )
                    in
                    if Dict.isEmpty onlyIn1 && Dict.isEmpty onlyIn2 then
                        {- Same field set on both sides -> the `r` in `{r | ...}`
                           must be the same for both sides.
                        -}
                        unifyMany cfg (( r1.extensionTypevar, r2.extensionTypevar ) :: sharedEqs)

                    else
                        State.do State.getNextIdAndTick <| \tailId ->
                        let
                            tail : MonoType
                            tail =
                                TypeI.id_ tailId
                        in
                        unifyMany
                            cfg
                            (( r1.extensionTypevar
                             , ExtensibleRecord
                                { extensionTypevar = tail
                                , fields = onlyIn2
                                }
                             )
                                :: ( r2.extensionTypevar
                                   , ExtensibleRecord
                                        { extensionTypevar = tail
                                        , fields = onlyIn1
                                        }
                                   )
                                :: sharedEqs
                            )

                Record r2Fields ->
                    unifyRecordVsExtensible cfg t1 t2 r2Fields r1

                _ ->
                    typeMismatch cfg t1 t2

        UserDefinedType ut1Raw ->
            case TypeI.userDefinedTypeExpandAliasAndCollapse cfg.typeAliases ut1Raw of
                (UserDefinedType ut1) as t1Expanded ->
                    case TypeI.expandAliasAndCollapse cfg.typeAliases t2 of
                        TypeVar v ->
                            bind cfg v t1Expanded

                        UserDefinedType ut2 ->
                            if
                                (ut1.package /= ut2.package)
                                    || ModuleIds.notEqual ut1.moduleId ut2.moduleId
                                    || (ut1.name /= ut2.name)
                            then
                                typeMismatch cfg t1 t2

                            else
                                case List.ExtraExtra.map2OrNothingIfLengthsDiffer ut1.args ut2.args of
                                    Nothing ->
                                        typeMismatch cfg t1 t2

                                    Just eqs ->
                                        unifyMany cfg eqs

                        _ ->
                            typeMismatch cfg t1 t2

                t1Expanded ->
                    unifyMono cfg t1Expanded t2

        WebGLShader webgl1 ->
            case t2 of
                TypeVar v ->
                    bind cfg v t1

                WebGLShader webgl2 ->
                    let
                        {- Unify one of a shader's attribute/uniform/varying sets.

                           Shader sets are special: the GLSL literal opens them, and a type
                           annotation can narrow them down to a closed record. So a closed
                           side only requires that its fields are present (with matching
                           types) in the other side; the open side absorbs the difference.
                           Two closed sides still have to agree on the field set.
                        -}
                        webglSet :
                            { extensionTypevar : MonoType, fields : Dict VarName MonoType }
                            -> { extensionTypevar : MonoType, fields : Dict VarName MonoType }
                            -> StateM ()
                        webglSet set1 set2 =
                            let
                                ( only1, only2, sharedEqs ) =
                                    Dict.merge
                                        (\k v ( o1, o2, eqs ) ->
                                            ( Dict.insert k v o1, o2, eqs )
                                        )
                                        (\_ v1 v2 ( o1, o2, eqs ) ->
                                            ( o1, o2, ( v1, v2 ) :: eqs )
                                        )
                                        (\k v ( o1, o2, eqs ) ->
                                            ( o1, Dict.insert k v o2, eqs )
                                        )
                                        set1.fields
                                        set2.fields
                                        ( Dict.empty, Dict.empty, [] )

                                isClosed : MonoType -> Bool
                                isClosed extensionTypevar =
                                    case extensionTypevar of
                                        Record _ ->
                                            True

                                        _ ->
                                            False

                                closed1 : Bool
                                closed1 =
                                    isClosed set1.extensionTypevar

                                closed2 : Bool
                                closed2 =
                                    isClosed set2.extensionTypevar
                            in
                            if closed1 && closed2 && not (Dict.isEmpty only1 && Dict.isEmpty only2) then
                                typeMismatch cfg t1 t2

                            else
                                State.do State.getNextIdAndTick <| \tailId ->
                                let
                                    tail : MonoType
                                    tail =
                                        TypeI.id_ tailId

                                    absorb : MonoType -> Dict VarName MonoType -> List ( MonoType, MonoType )
                                    absorb extensionTypevar fields =
                                        [ ( extensionTypevar
                                          , ExtensibleRecord
                                                { extensionTypevar = tail
                                                , fields = fields
                                                }
                                          )
                                        ]
                                in
                                if not closed1 && not closed2 then
                                    unifyMany cfg (absorb set1.extensionTypevar only2 ++ absorb set2.extensionTypevar only1 ++ sharedEqs)

                                else if not closed1 then
                                    unifyMany cfg (absorb set1.extensionTypevar only2 ++ sharedEqs)

                                else if not closed2 then
                                    unifyMany cfg (absorb set2.extensionTypevar only1 ++ sharedEqs)

                                else
                                    unifyMany cfg sharedEqs
                    in
                    State.do
                        (webglSet
                            { extensionTypevar = webgl1.attributesExtension
                            , fields = webgl1.attributes
                            }
                            { extensionTypevar = webgl2.attributesExtension
                            , fields = webgl2.attributes
                            }
                        )
                    <| \() ->
                    State.do
                        (webglSet
                            { extensionTypevar = webgl1.uniformsExtension
                            , fields = webgl1.uniforms
                            }
                            { extensionTypevar = webgl2.uniformsExtension
                            , fields = webgl2.uniforms
                            }
                        )
                    <| \() ->
                    webglSet
                        { extensionTypevar = webgl1.varyingsExtension
                        , fields = webgl1.varyings
                        }
                        { extensionTypevar = webgl2.varyingsExtension
                        , fields = webgl2.varyings
                        }

                _ ->
                    typeMismatch cfg t1 t2


{-| Binds an unbound typeVar root with a given monotype.
Both are already substituted.
-}
bind : UnifyConfig -> TypeVar -> MonoType -> StateM ()
bind cfg typeVar type_ =
    case type_ of
        TypeVar otherVar ->
            if TypeVar.equal otherVar typeVar then
                State.pureUnit

            else
                let
                    ( otherStyle, otherSuper ) =
                        otherVar

                    ( style, super ) =
                        typeVar
                in
                case meet super otherSuper of
                    Nothing ->
                        let
                            ( pubVar, pubOther ) =
                                TypeI.normalizeAndToPublicPair cfg.moduleMapping (TypeVar typeVar) type_
                        in
                        State.error
                            { moduleName = FullModuleName.toModuleName cfg.moduleName
                            , declarationNames = cfg.declarationNames
                            , details = ConstraintMismatch pubVar pubOther
                            }

                    Just m ->
                        if TypeVar.superTypeEqual m super && TypeVar.superTypeEqual m otherSuper then
                            -- Either could be chosen as then parent (linked to),
                            -- but we prefer Generated ids as they can't collide.
                            State.modifySubst <| \subst ->
                            case style of
                                Named _ ->
                                    case otherStyle of
                                        Generated _ ->
                                            subst |> SubstitutionMap.linkTo { child = typeVar, parent = otherVar }

                                        Named _ ->
                                            subst |> SubstitutionMap.union typeVar otherVar

                                Generated _ ->
                                    case otherStyle of
                                        Named _ ->
                                            subst |> SubstitutionMap.linkTo { child = otherVar, parent = typeVar }

                                        Generated _ ->
                                            subst |> SubstitutionMap.union typeVar otherVar

                        else if TypeVar.superTypeEqual m otherSuper then
                            -- otherVar is more constrained -> it will be the `parent` representative.
                            State.modifySubst (\subst -> subst |> SubstitutionMap.linkTo { child = typeVar, parent = otherVar })

                        else if TypeVar.superTypeEqual m super then
                            State.modifySubst (\subst -> subst |> SubstitutionMap.linkTo { child = otherVar, parent = typeVar })

                        else
                            -- eg. Comparable and Appendable
                            -- introduce fresh var with combined constraint
                            -- point both at it
                            State.do State.getNextIdAndTick <| \freshId ->
                            let
                                fresh : TypeVar
                                fresh =
                                    ( Generated freshId, m )
                            in
                            State.modifySubst
                                (\subst ->
                                    subst
                                        |> SubstitutionMap.linkTo { child = typeVar, parent = fresh }
                                        |> SubstitutionMap.linkTo { child = otherVar, parent = fresh }
                                )

        _ ->
            if occursCheck typeVar type_ then
                let
                    ( pubVar, pubType ) =
                        TypeI.normalizeAndToPublicPair cfg.moduleMapping (TypeVar typeVar) type_
                in
                State.error
                    { moduleName = FullModuleName.toModuleName cfg.moduleName
                    , declarationNames = cfg.declarationNames
                    , details = InfiniteType pubVar pubType
                    }

            else
                let
                    ( _, super ) =
                        typeVar

                    typeExpanded : MonoType
                    typeExpanded =
                        -- TODO don't expand once normalizeAndToPublicType has been changed
                        TypeI.expandAliasAndCollapse cfg.typeAliases type_
                in
                if accepts super typeExpanded then
                    State.modifySubst
                        (\subst ->
                            SubstitutionMap.bindRoot typeVar
                                typeExpanded
                                subst
                        )

                else
                    let
                        ( pubVar, pubType ) =
                            TypeI.normalizeAndToPublicPair cfg.moduleMapping
                                (TypeVar typeVar)
                                typeExpanded
                    in
                    State.error
                        { moduleName = FullModuleName.toModuleName cfg.moduleName
                        , declarationNames = cfg.declarationNames
                        , details = ConstraintMismatch pubVar pubType
                        }


{-| The most specific supertype that satisfies both constraints, if any.
-}
meet : SuperType -> SuperType -> Maybe SuperType
meet a b =
    case a of
        Normal ->
            Just b

        Number ->
            case b of
                Normal ->
                    Just Number

                Comparable ->
                    Just Number

                CompAppend ->
                    Nothing

                Appendable ->
                    Nothing

                Number ->
                    Just Number

        Comparable ->
            case b of
                Normal ->
                    Just Comparable

                Number ->
                    Just Number

                Appendable ->
                    Just CompAppend

                CompAppend ->
                    Just CompAppend

                Comparable ->
                    Just Comparable

        Appendable ->
            case b of
                Normal ->
                    Just Appendable

                Comparable ->
                    Just CompAppend

                CompAppend ->
                    Just CompAppend

                Number ->
                    Nothing

                Appendable ->
                    Just Appendable

        CompAppend ->
            case b of
                Normal ->
                    Just CompAppend

                Comparable ->
                    Just CompAppend

                Appendable ->
                    Just CompAppend

                Number ->
                    Nothing

                CompAppend ->
                    Just CompAppend


accepts : SuperType -> MonoType -> Bool
accepts super type_ =
    case super of
        Normal ->
            True

        Number ->
            case type_ of
                Int ->
                    True

                Float ->
                    True

                _ ->
                    False

        Comparable ->
            isComparable type_

        Appendable ->
            isAppendable type_

        CompAppend ->
            isComparable type_ && isAppendable type_


isComparable : MonoType -> Bool
isComparable type_ =
    case type_ of
        Int ->
            True

        Float ->
            True

        Char ->
            True

        String ->
            True

        List inner ->
            isComparable inner

        Tuple2 a b ->
            -- && but with a bit of TCO
            if isComparable a then
                isComparable b

            else
                False

        Tuple3 a b c ->
            -- && but with a bit of TCO
            if isComparable a && isComparable b then
                isComparable c

            else
                False

        TypeVar _ ->
            True

        Function _ ->
            False

        Bool ->
            False

        Unit ->
            False

        Record _ ->
            False

        ExtensibleRecord _ ->
            False

        UserDefinedType _ ->
            False

        WebGLShader _ ->
            False


isAppendable : MonoType -> Bool
isAppendable type_ =
    case type_ of
        String ->
            True

        List _ ->
            True

        TypeVar _ ->
            True

        Int ->
            False

        Float ->
            False

        Char ->
            False

        Tuple2 _ _ ->
            False

        Tuple3 _ _ _ ->
            False

        Function _ ->
            False

        Bool ->
            False

        Unit ->
            False

        Record _ ->
            False

        ExtensibleRecord _ ->
            False

        UserDefinedType _ ->
            False

        WebGLShader _ ->
            False


{-| Does `typeVar` occur anywhere in `type_`?
-}
occursCheck : TypeVar -> MonoType -> Bool
occursCheck typeVar type_ =
    case type_ of
        TypeVar var ->
            TypeVar.equal var typeVar

        Function { from, to } ->
            occursCheck typeVar from || occursCheck typeVar to

        Int ->
            False

        Float ->
            False

        Char ->
            False

        String ->
            False

        Bool ->
            False

        List listItemType ->
            occursCheck typeVar listItemType

        Unit ->
            False

        Tuple2 t1 t2 ->
            occursCheck typeVar t1 || occursCheck typeVar t2

        Tuple3 t1 t2 t3 ->
            occursCheck typeVar t1
                || occursCheck typeVar t2
                || occursCheck typeVar t3

        Record fields ->
            Dict.Extra.any (\_ v -> occursCheck typeVar v) fields

        ExtensibleRecord r ->
            occursCheck typeVar r.extensionTypevar
                || Dict.Extra.any (\_ v -> occursCheck typeVar v) r.fields

        UserDefinedType r ->
            List.any (\arg -> occursCheck typeVar arg) r.args

        WebGLShader r ->
            occursCheck typeVar r.attributesExtension
                || Dict.Extra.any (\_ v -> occursCheck typeVar v) r.attributes
                || occursCheck typeVar r.uniformsExtension
                || Dict.Extra.any (\_ v -> occursCheck typeVar v) r.uniforms
                || occursCheck typeVar r.varyingsExtension
                || Dict.Extra.any (\_ v -> occursCheck typeVar v) r.varyings
