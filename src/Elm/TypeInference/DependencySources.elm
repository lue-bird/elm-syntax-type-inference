module Elm.TypeInference.DependencySources exposing (neededSources, referencedModules)

{-| Get type alias bodies from dependency source files.
We need the alias bodies to know if they're records or unions, for type inference later.
-}

import Dict exposing (Dict)
import Elm.Docs
import Elm.Syntax.File exposing (File)
import Elm.Syntax.File.Extra as FileExtra
import Elm.Syntax.ModuleName.Extra as ModuleNameExtra
import Elm.TypeInference.Dependencies as Dependencies exposing (Dependencies)
import Elm.TypeInference.Type exposing (PackageName)
import Set exposing (Set)


{-| Every dotted module name referenced anywhere in docs.json types.

docs.json values can mention unexposed modules (e.g. `Css.pct` returns
`Css.Internal.ExplicitLength`). We need to intern those too.

-}
referencedModules : Dependencies -> List String
referencedModules deps =
    let
        allModules : List Elm.Docs.Module
        allModules =
            Dict.foldr (\_ { modules } acc -> List.append modules acc) [] deps

        addNameIfUnique : String -> List String -> List String
        addNameIfUnique name names =
            if String.isEmpty name || List.member name names then
                names

            else
                name :: names
    in
    List.foldl (\( name, _ ) acc -> addNameIfUnique name acc)
        []
        (List.foldl
            (\mod acc -> Dependencies.addDocsModuleRefsToList mod acc)
            []
            allModules
        )
        |> (\accWithoutModNames ->
                List.foldl (\mod acc -> addNameIfUnique mod.name acc) accWithoutModNames allModules
           )


{-| Which packages' `docs.json` types use unknown modules, or types that
aren't exposed (eg. a `type alias` used in an exposed function's signature,
but not itself in the module's `exposing` list)?

docs.json can't tell us the underlying (record) shape of such a type, so we
need the actual source to know whether it's a record we can unify
structurally against.

-}
neededSources : Dependencies -> Dict PackageName (List File) -> List ( PackageName, List String )
neededSources deps sources =
    let
        docsTypes : Dict String (Set String)
        docsTypes =
            deps
                |> Dict.foldl
                    (\_ dep accAcrossDeps ->
                        dep.modules
                            |> List.foldl
                                (\mod acc ->
                                    let
                                        value : Set String
                                        value =
                                            case Dict.get mod.name acc of
                                                Just existing ->
                                                    Set.union
                                                        (documentedTypeNames mod)
                                                        existing

                                                Nothing ->
                                                    documentedTypeNames mod
                                    in
                                    Dict.insert mod.name value acc
                                )
                                accAcrossDeps
                    )
                    Dict.empty
    in
    deps
        |> Dict.foldr
            (\package pkg needsSourcesAcc ->
                let
                    supplied : Set String
                    supplied =
                        suppliedModuleNames package sources

                    remaining : Set String
                    remaining =
                        pkg.modules
                            |> List.foldl
                                (\mod acc -> Dependencies.addDocsModuleRefsToList mod acc)
                                []
                            |> List.foldl
                                (\(( m, _ ) as ref) acc ->
                                    if isKnownRef docsTypes ref || Set.member m supplied then
                                        acc

                                    else
                                        Set.insert m acc
                                )
                                Set.empty
                in
                if Set.isEmpty remaining then
                    needsSourcesAcc

                else
                    ( package
                    , Set.foldr (\m acc -> ModuleNameExtra.dottedToFilePath m :: acc) [] remaining
                    )
                        :: needsSourcesAcc
            )
            []


suppliedModuleNames : PackageName -> Dict PackageName (List File) -> Set String
suppliedModuleNames package sources =
    case Dict.get package sources of
        Just files ->
            files
                |> List.foldl (\m acc -> Set.insert (fileDottedName m) acc)
                    Set.empty

        Nothing ->
            Set.empty


fileDottedName : File -> String
fileDottedName file =
    FileExtra.moduleName file
        |> ModuleNameExtra.toString


documentedTypeNames : Elm.Docs.Module -> Set String
documentedTypeNames mod =
    List.foldl (\union acc -> Set.insert union.name acc)
        (List.foldl (\typeAlias acc -> Set.insert typeAlias.name acc)
            Set.empty
            mod.aliases
        )
        mod.unions


isKnownRef : Dict String (Set String) -> ( String, String ) -> Bool
isKnownRef docsTypes ( moduleName, typeName ) =
    case Dict.get moduleName docsTypes of
        Nothing ->
            False

        Just typeNames ->
            Set.member typeName typeNames
