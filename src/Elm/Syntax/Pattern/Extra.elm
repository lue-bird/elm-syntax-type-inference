module Elm.Syntax.Pattern.Extra exposing (foldVarNames, insertVarNamesIntoSet, varNames)

import Elm.Syntax.Node as Node
import Elm.Syntax.Pattern exposing (Pattern(..))
import Elm.TypeInference.Type exposing (VarName)
import Set exposing (Set)


{-| Collect vars from a pattern.
Prefer `insertVarNamesIntoSet` or `varNamesFold` if you want anything other than a lis of names
-}
varNames : Pattern -> List VarName
varNames pattern =
    varNamesInto pattern []


varNamesInto : Pattern -> List VarName -> List VarName
varNamesInto pattern acc =
    case pattern of
        VarPattern var ->
            var :: acc

        AllPattern ->
            acc

        UnitPattern ->
            acc

        CharPattern _ ->
            acc

        StringPattern _ ->
            acc

        IntPattern _ ->
            acc

        HexPattern _ ->
            acc

        FloatPattern _ ->
            acc

        TuplePattern patterns ->
            List.foldl
                (\(Node.Node _ part) acrossParts -> varNamesInto part acrossParts)
                acc
                patterns

        RecordPattern fields ->
            List.foldl
                (\(Node.Node _ fieldName) acrossFields -> fieldName :: acrossFields)
                acc
                fields

        UnConsPattern p1 p2 ->
            varNamesInto (Node.value p1) (varNamesInto (Node.value p2) acc)

        ListPattern patterns ->
            List.foldl
                (\(Node.Node _ element) acrossElements -> varNamesInto element acrossElements)
                acc
                patterns

        NamedPattern _ patterns ->
            List.foldl
                (\(Node.Node _ payload) acrossPayloads -> varNamesInto payload acrossPayloads)
                acc
                patterns

        AsPattern p1 name ->
            varNamesInto (Node.value p1) (Node.value name :: acc)

        ParenthesizedPattern p1 ->
            varNames (Node.value p1)


{-| Collect vars from a pattern into a given Set
-}
insertVarNamesIntoSet : Pattern -> Set VarName -> Set VarName
insertVarNamesIntoSet pattern acc =
    case pattern of
        VarPattern var ->
            Set.insert var acc

        AllPattern ->
            acc

        UnitPattern ->
            acc

        CharPattern _ ->
            acc

        StringPattern _ ->
            acc

        IntPattern _ ->
            acc

        HexPattern _ ->
            acc

        FloatPattern _ ->
            acc

        TuplePattern patterns ->
            List.foldl
                (\(Node.Node _ part) accAcrossParts -> insertVarNamesIntoSet part accAcrossParts)
                acc
                patterns

        RecordPattern fields ->
            List.foldl
                (\(Node.Node _ fieldName) accAcrossFields -> Set.insert fieldName accAcrossFields)
                acc
                fields

        UnConsPattern p1 p2 ->
            insertVarNamesIntoSet (Node.value p1) (insertVarNamesIntoSet (Node.value p2) acc)

        ListPattern patterns ->
            List.foldl
                (\(Node.Node _ element) accAcrossElements -> insertVarNamesIntoSet element accAcrossElements)
                acc
                patterns

        NamedPattern _ patterns ->
            List.foldl
                (\(Node.Node _ payload) accAcrossPayloads -> insertVarNamesIntoSet payload accAcrossPayloads)
                acc
                patterns

        AsPattern p1 name ->
            Set.insert (Node.value name) (insertVarNamesIntoSet (Node.value p1) acc)

        ParenthesizedPattern p1 ->
            insertVarNamesIntoSet (Node.value p1) acc


foldVarNames : (String -> acc -> acc) -> acc -> Pattern -> acc
foldVarNames reduce acc pattern =
    case pattern of
        VarPattern var ->
            reduce var acc

        AllPattern ->
            acc

        UnitPattern ->
            acc

        CharPattern _ ->
            acc

        StringPattern _ ->
            acc

        IntPattern _ ->
            acc

        HexPattern _ ->
            acc

        FloatPattern _ ->
            acc

        TuplePattern patterns ->
            List.foldl
                (\(Node.Node _ part) accAcrossParts -> foldVarNames reduce accAcrossParts part)
                acc
                patterns

        RecordPattern fields ->
            List.foldl
                (\(Node.Node _ fieldName) accAcrossFields -> reduce fieldName accAcrossFields)
                acc
                fields

        UnConsPattern p1 p2 ->
            foldVarNames reduce (foldVarNames reduce acc (Node.value p2)) (Node.value p1)

        ListPattern patterns ->
            List.foldl
                (\(Node.Node _ element) accAcrossElements -> foldVarNames reduce accAcrossElements element)
                acc
                patterns

        NamedPattern _ patterns ->
            List.foldl
                (\(Node.Node _ payload) accAcrossPayloads -> foldVarNames reduce accAcrossPayloads payload)
                acc
                patterns

        AsPattern p1 name ->
            foldVarNames reduce (reduce (Node.value name) acc) (Node.value p1)

        ParenthesizedPattern p1 ->
            foldVarNames reduce acc (Node.value p1)
