module Elm.Syntax.Expression.Extra exposing (functionName, referencedNames)

import Elm.Syntax.Expression exposing (Expression(..), Function, LetDeclaration(..))
import Elm.Syntax.ModuleName exposing (ModuleName)
import Elm.Syntax.Node as Node exposing (Node)
import Elm.Syntax.Pattern.Extra
import Elm.TypeInference.Type exposing (VarName)
import Set exposing (Set)


functionName : Function -> String
functionName function =
    function.declaration
        |> Node.value
        |> .name
        |> Node.value


{-| Collects value names (not patterns).
Useful for binding-group SCC logic later.
-}
referencedNames : Expression -> List ( Maybe ModuleName, VarName )
referencedNames expression =
    referencedNamesInBoundIntoList Set.empty expression []


{-| Like `referencedNames`, but excludes unqualified names bound by an enclosing
lambda, pattern or nested `let`.

This is important for binding-group logic: a locally shadowed name must not
create a dependency on outer declaration of the same name.

-}
referencedNamesInBoundIntoList :
    Set VarName
    -> Expression
    -> List ( Maybe ModuleName, VarName )
    -> List ( Maybe ModuleName, VarName )
referencedNamesInBoundIntoList bound expression acc =
    case expression of
        FunctionOrValue moduleName varName ->
            if List.isEmpty moduleName then
                if Set.member varName bound then
                    acc

                else
                    ( Nothing, varName ) :: acc

            else
                ( Just moduleName, varName ) :: acc

        PrefixOperator operator ->
            ( Nothing, operator ) :: acc

        OperatorApplication operator _ e1 e2 ->
            ( Nothing, operator )
                :: referencedNamesInBoundIntoList bound
                    (Node.value e1)
                    (referencedNamesInBoundIntoList bound (Node.value e2) acc)

        Application nodes ->
            List.foldl
                (\(Node.Node _ p) acrossParts ->
                    referencedNamesInBoundIntoList bound p acrossParts
                )
                acc
                nodes

        IfBlock e1 e2 e3 ->
            referencedNamesInBoundIntoList bound
                (Node.value e1)
                (referencedNamesInBoundIntoList bound
                    (Node.value e2)
                    (referencedNamesInBoundIntoList bound (Node.value e3) acc)
                )

        Negation e1 ->
            referencedNamesInBoundIntoList bound (Node.value e1) acc

        TupledExpression nodes ->
            List.foldl
                (\(Node.Node _ p) acrossParts ->
                    referencedNamesInBoundIntoList bound p acrossParts
                )
                acc
                nodes

        ParenthesizedExpression e1 ->
            referencedNamesInBoundIntoList bound (Node.value e1) acc

        LetExpression letBlock ->
            let
                nestedBound : Set VarName
                nestedBound =
                    letBlock.declarations
                        |> List.foldl
                            (\(Node.Node _ declaration) acrossDecls ->
                                case declaration of
                                    LetFunction fn ->
                                        Set.insert (functionName fn) acrossDecls

                                    LetDestructuring patternNode _ ->
                                        Elm.Syntax.Pattern.Extra.insertVarNamesIntoSet
                                            (Node.value patternNode)
                                            acrossDecls
                            )
                            bound

                declRefs : Node LetDeclaration -> List ( Maybe ModuleName, VarName ) -> List ( Maybe ModuleName, VarName )
                declRefs declNode declAcc =
                    case Node.value declNode of
                        LetFunction fn ->
                            let
                                nestedBoundIncludingArgumentNames : Set VarName
                                nestedBoundIncludingArgumentNames =
                                    (Node.value fn.declaration).arguments
                                        |> List.foldl
                                            (\(Node.Node _ arg) acrossArgs ->
                                                Elm.Syntax.Pattern.Extra.insertVarNamesIntoSet arg acrossArgs
                                            )
                                            nestedBound
                            in
                            referencedNamesInBoundIntoList nestedBoundIncludingArgumentNames
                                (Node.value (Node.value fn.declaration).expression)
                                declAcc

                        LetDestructuring _ e1 ->
                            referencedNamesInBoundIntoList nestedBound (Node.value e1) declAcc
            in
            letBlock.declarations
                |> List.foldl declRefs
                    (referencedNamesInBoundIntoList nestedBound
                        (Node.value letBlock.expression)
                        acc
                    )

        CaseExpression caseBlock ->
            referencedNamesInBoundIntoList bound
                (Node.value caseBlock.expression)
                (List.foldl
                    (\( pattern, body ) acrossCases ->
                        referencedNamesInBoundIntoList
                            (Elm.Syntax.Pattern.Extra.insertVarNamesIntoSet (Node.value pattern) bound)
                            (Node.value body)
                            acrossCases
                    )
                    acc
                    caseBlock.cases
                )

        LambdaExpression lambda ->
            let
                boundIncludingArgumentNames : Set String
                boundIncludingArgumentNames =
                    lambda.args
                        |> List.foldl
                            (\(Node.Node _ param) acrossArgs ->
                                Elm.Syntax.Pattern.Extra.insertVarNamesIntoSet param acrossArgs
                            )
                            bound
            in
            referencedNamesInBoundIntoList boundIncludingArgumentNames
                (Node.value lambda.expression)
                acc

        RecordExpr setters ->
            setters
                |> List.foldl
                    (\(Node.Node _ ( _, Node.Node _ value )) acrossFields ->
                        referencedNamesInBoundIntoList bound value acrossFields
                    )
                    acc

        ListExpr nodes ->
            List.foldl
                (\(Node.Node _ el) acrossElements ->
                    referencedNamesInBoundIntoList bound el acrossElements
                )
                acc
                nodes

        RecordAccess recordNode _ ->
            referencedNamesInBoundIntoList bound (Node.value recordNode) acc

        RecordAccessFunction _ ->
            acc

        RecordUpdateExpression recordVarNode setters ->
            ( Nothing, Node.value recordVarNode )
                :: (setters
                        |> List.foldl
                            (\(Node.Node _ ( _, Node.Node _ value )) acrossFields ->
                                referencedNamesInBoundIntoList bound value acrossFields
                            )
                            acc
                   )

        GLSLExpression _ ->
            acc

        UnitExpr ->
            acc

        Integer _ ->
            acc

        Hex _ ->
            acc

        Floatable _ ->
            acc

        Literal _ ->
            acc

        CharLiteral _ ->
            acc

        Operator _ ->
            acc
