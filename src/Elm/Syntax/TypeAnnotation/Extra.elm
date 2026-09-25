module Elm.Syntax.TypeAnnotation.Extra exposing (referencesToTypesFromModuleId)

import Elm.Syntax.Node as Node
import Elm.Syntax.TypeAnnotation as TypeAnnotation exposing (TypeAnnotation)
import Elm.TypeInference.ModuleIds as ModuleIds exposing (ModuleId)
import Elm.TypeInference.Type.Internal as TypeI


referencesToTypesFromModuleId : TypeI.TypeResolver -> ModuleId -> TypeAnnotation -> List String
referencesToTypesFromModuleId resolver ownModuleId typeAnnotation =
    referencesToTypesFromModuleIdHelp resolver ownModuleId typeAnnotation []


referencesToTypesFromModuleIdHelp : TypeI.TypeResolver -> ModuleId -> TypeAnnotation -> List String -> List String
referencesToTypesFromModuleIdHelp resolver ownModuleId typeAnnotation acc =
    case typeAnnotation of
        TypeAnnotation.Unit ->
            acc

        TypeAnnotation.GenericType _ ->
            acc

        TypeAnnotation.Typed (Node.Node _ ( qualification, name )) args ->
            args
                |> List.foldl
                    (\(Node.Node _ arg) accAcrossArgs ->
                        referencesToTypesFromModuleIdHelp resolver ownModuleId arg accAcrossArgs
                    )
                    (case resolver qualification name of
                        Err _ ->
                            acc

                        Ok ( package, moduleId ) ->
                            if package == "" && ModuleIds.equal moduleId ownModuleId then
                                name :: acc

                            else
                                acc
                    )

        TypeAnnotation.Tupled parts ->
            parts
                |> List.foldl
                    (\(Node.Node _ part) accAcrossParts ->
                        referencesToTypesFromModuleIdHelp resolver ownModuleId part accAcrossParts
                    )
                    acc

        TypeAnnotation.Record fields ->
            fields
                |> List.foldl
                    (\(Node.Node _ ( _, Node.Node _ value )) accAcrossFields ->
                        referencesToTypesFromModuleIdHelp resolver ownModuleId value accAcrossFields
                    )
                    acc

        TypeAnnotation.GenericRecord _ (Node.Node _ fields) ->
            fields
                |> List.foldl
                    (\(Node.Node _ ( _, Node.Node _ value )) accAcrossFields ->
                        referencesToTypesFromModuleIdHelp resolver ownModuleId value accAcrossFields
                    )
                    acc

        TypeAnnotation.FunctionTypeAnnotation (Node.Node _ inType) (Node.Node _ outType) ->
            referencesToTypesFromModuleIdHelp resolver
                ownModuleId
                outType
                (referencesToTypesFromModuleIdHelp resolver ownModuleId inType acc)
