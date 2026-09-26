module Elm.TypeInference.Dependencies exposing
    ( Dependencies
    , DependencyPackage
    , Resolver
    , addDocsModuleRefNamesToList
    , addDocsModuleRefsToList
    , addDocsTypeRefsWithSameModuleNameToList
    , fromList
    )

{-| Dependency types from docs.json.
-}

import Dict exposing (Dict)
import Elm.Docs
import Elm.Syntax.ModuleName.Extra as ModuleNameExtra
import Elm.Type
import Elm.TypeInference.Error exposing (ErrorDetails(..))
import Elm.TypeInference.ModuleIds exposing (ModuleId)
import Elm.TypeInference.Type exposing (PackageName, VarName)
import Elm.TypeInference.Type.Internal as TypeI exposing (MonoType(..))
import Elm.TypeInference.TypeVar as TypeVar
import Elm.TypeInference.Unify exposing (TypeAlias)
import Result.Extra


type alias DependencyPackage =
    { name : PackageName
    , dependencies : List PackageName
    , modules : List Elm.Docs.Module
    }


type alias Dependencies =
    Dict PackageName DependencyPackage


{-| Resolves a module name from docs.json to its package.
-}
type alias Resolver =
    String -> Result ErrorDetails ( PackageName, ModuleId )


fromList : List DependencyPackage -> Dependencies
fromList packages =
    packages
        |> List.foldl (\pkg acc -> Dict.insert pkg.name pkg acc)
            Dict.empty


fromDocsType :
    Resolver
    -> Dict ( ModuleId, PackageName, VarName ) TypeAlias
    -> Elm.Type.Type
    -> Result ErrorDetails MonoType
fromDocsType resolver typeAliases type_ =
    case type_ of
        Elm.Type.Var name ->
            Ok (TypeVar (TypeVar.parse name))

        Elm.Type.Lambda from to ->
            Result.map2 (\f t -> Function { from = f, to = t })
                (fromDocsType resolver typeAliases from)
                (fromDocsType resolver typeAliases to)

        Elm.Type.Tuple [] ->
            Ok Unit

        Elm.Type.Tuple [ a, b ] ->
            Result.map2 Tuple2
                (fromDocsType resolver typeAliases a)
                (fromDocsType resolver typeAliases b)

        Elm.Type.Tuple [ a, b, c ] ->
            Result.map3 Tuple3
                (fromDocsType resolver typeAliases a)
                (fromDocsType resolver typeAliases b)
                (fromDocsType resolver typeAliases c)

        Elm.Type.Tuple _ ->
            Err (ImpossibleDocsType type_)

        Elm.Type.Type qualifiedName args ->
            let
                ( moduleNameStr, typeName ) =
                    ModuleNameExtra.splitLastDot qualifiedName
            in
            Result.map2
                (\( package, moduleId ) argTypes ->
                    TypeI.fromTyped typeAliases package moduleId typeName argTypes
                )
                (resolver moduleNameStr)
                (Result.Extra.combineMap (\arg -> fromDocsType resolver typeAliases arg) args)

        Elm.Type.Record fields Nothing ->
            dictFromDocsFields resolver typeAliases fields
                |> Result.map Record

        Elm.Type.Record fields (Just rowVar) ->
            dictFromDocsFields resolver typeAliases fields
                |> Result.map
                    (\resolvedFields ->
                        ExtensibleRecord
                            { extensionTypevar = TypeVar (TypeVar.parse rowVar)
                            , fields = resolvedFields
                            }
                    )


dictFromDocsFields :
    Resolver
    -> Dict ( ModuleId, PackageName, VarName ) TypeAlias
    -> List ( String, Elm.Type.Type )
    -> Result ErrorDetails (Dict String MonoType)
dictFromDocsFields resolver typeAliases fields =
    Result.Extra.foldlWhileOk
        (\( name, value ) acc ->
            fromDocsType resolver typeAliases value
                |> Result.map (\valueType -> Dict.insert name valueType acc)
        )
        Dict.empty
        fields


addDocsModuleRefsToList : Elm.Docs.Module -> List ( String, String ) -> List ( String, String )
addDocsModuleRefsToList mod accAcrossModules =
    List.foldl (\value acc -> acc |> addDocsTypeRefsToList value.tipe)
        accAcrossModules
        mod.values
        |> (\acc ->
                List.foldl
                    (\binop accAcrossBinops -> accAcrossBinops |> addDocsTypeRefsToList binop.tipe)
                    acc
                    mod.binops
           )
        |> (\acc ->
                List.foldl
                    (\union accAcrossUnions ->
                        List.foldl
                            (\( _, payload ) accAcrossPayloads ->
                                List.foldl addDocsTypeRefsToList accAcrossPayloads payload
                            )
                            accAcrossUnions
                            union.tags
                    )
                    acc
                    mod.unions
           )
        |> (\acc ->
                List.foldl
                    (\typeAlias accAcrossTypeAliases -> addDocsTypeRefsToList typeAlias.tipe accAcrossTypeAliases)
                    acc
                    mod.aliases
           )


addDocsModuleRefNamesToList : Elm.Docs.Module -> List String -> List String
addDocsModuleRefNamesToList mod accAcrossModules =
    List.foldl (\value acc -> acc |> addDocsTypeRefNamesToList value.tipe)
        accAcrossModules
        mod.values
        |> (\acc ->
                List.foldl
                    (\binop accAcrossBinops -> accAcrossBinops |> addDocsTypeRefNamesToList binop.tipe)
                    acc
                    mod.binops
           )
        |> (\acc ->
                List.foldl
                    (\union accAcrossUnions ->
                        List.foldl
                            (\( _, payload ) accAcrossPayloads ->
                                List.foldl addDocsTypeRefNamesToList accAcrossPayloads payload
                            )
                            accAcrossUnions
                            union.tags
                    )
                    acc
                    mod.unions
           )
        |> (\acc ->
                List.foldl
                    (\typeAlias accAcrossTypeAliases -> addDocsTypeRefNamesToList typeAlias.tipe accAcrossTypeAliases)
                    acc
                    mod.aliases
           )


addDocsTypeRefsToList : Elm.Type.Type -> List ( String, String ) -> List ( String, String )
addDocsTypeRefsToList tipe acc =
    case tipe of
        Elm.Type.Var _ ->
            acc

        Elm.Type.Lambda from to ->
            addDocsTypeRefsToList from (addDocsTypeRefsToList to acc)

        Elm.Type.Tuple parts ->
            List.foldl addDocsTypeRefsToList acc parts

        Elm.Type.Type qualifiedName args ->
            let
                ( moduleName, typeName ) =
                    ModuleNameExtra.splitLastDot qualifiedName

                accAndArgsRefs : List ( String, String )
                accAndArgsRefs =
                    List.foldl addDocsTypeRefsToList acc args
            in
            -- Skip elm/core stuff
            if isPrimitiveRef moduleName typeName then
                accAndArgsRefs

            else if String.isEmpty moduleName then
                accAndArgsRefs

            else
                ( moduleName, typeName ) :: accAndArgsRefs

        Elm.Type.Record fields _ ->
            List.foldl
                (\( _, value ) accAcrossFields -> accAcrossFields |> addDocsTypeRefsToList value)
                acc
                fields


addDocsTypeRefNamesToList : Elm.Type.Type -> List String -> List String
addDocsTypeRefNamesToList tipe acc =
    case tipe of
        Elm.Type.Var _ ->
            acc

        Elm.Type.Lambda from to ->
            addDocsTypeRefNamesToList from (addDocsTypeRefNamesToList to acc)

        Elm.Type.Tuple parts ->
            List.foldl addDocsTypeRefNamesToList acc parts

        Elm.Type.Type qualifiedName args ->
            let
                ( moduleName, typeName ) =
                    ModuleNameExtra.splitLastDot qualifiedName

                accAndArgsRefs : List String
                accAndArgsRefs =
                    List.foldl addDocsTypeRefNamesToList acc args
            in
            -- Skip elm/core stuff
            if isPrimitiveRef moduleName typeName then
                accAndArgsRefs

            else if String.isEmpty moduleName then
                accAndArgsRefs

            else
                moduleName :: accAndArgsRefs

        Elm.Type.Record fields _ ->
            List.foldl
                (\( _, value ) accAcrossFields -> accAcrossFields |> addDocsTypeRefNamesToList value)
                acc
                fields


addDocsTypeRefsWithSameModuleNameToList : String -> Elm.Type.Type -> List String -> List String
addDocsTypeRefsWithSameModuleNameToList requestedModuleName tipe acc =
    case tipe of
        Elm.Type.Var _ ->
            acc

        Elm.Type.Lambda from to ->
            addDocsTypeRefsWithSameModuleNameToList requestedModuleName
                from
                (addDocsTypeRefsWithSameModuleNameToList requestedModuleName to acc)

        Elm.Type.Tuple parts ->
            List.foldl
                (\part acrossParts ->
                    addDocsTypeRefsWithSameModuleNameToList requestedModuleName part acrossParts
                )
                acc
                parts

        Elm.Type.Type qualifiedName args ->
            let
                ( moduleName, typeName ) =
                    ModuleNameExtra.splitLastDot qualifiedName

                accAndArgsRefs : List String
                accAndArgsRefs =
                    List.foldl
                        (\arg acrossArgs ->
                            addDocsTypeRefsWithSameModuleNameToList requestedModuleName arg acrossArgs
                        )
                        acc
                        args
            in
            if requestedModuleName == moduleName then
                typeName :: accAndArgsRefs

            else
                accAndArgsRefs

        Elm.Type.Record fields _ ->
            List.foldl
                (\( _, value ) accAcrossFields ->
                    accAcrossFields |> addDocsTypeRefsWithSameModuleNameToList requestedModuleName value
                )
                acc
                fields


isPrimitiveRef : String -> String -> Bool
isPrimitiveRef moduleName typeName =
    case moduleName of
        "Basics" ->
            case typeName of
                "Int" ->
                    True

                "Float" ->
                    True

                "Bool" ->
                    True

                _ ->
                    False

        "Char" ->
            typeName == "Char"

        "String" ->
            typeName == "String"

        "List" ->
            typeName == "List"

        _ ->
            False
