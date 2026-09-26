module Elm.TypeInference exposing
    ( dependencyEnv, DependencyEnvOutcome(..), DependencyEnv, Dependency
    , project, Project
    , inferModule, inferModules
    , addFile, removeFile
    )

{-| Type inference for
[`elm-syntax`](https://package.elm-lang.org/packages/stil4m/elm-syntax/latest/)
ASTs.

Optimized for lazy queries `Range -> Maybe Type`.

The process:

  - Convert `elm.json` and dependencies' `elm.json` + `docs.json` into
    [`DependencyEnv`](#DependencyEnv).
  - Load the
    [`File`](https://package.elm-lang.org/packages/stil4m/elm-syntax/latest/Elm-Syntax-File#File)s
    into a [`Project`](#Project).
  - (When it's clear you need it) Infer a module with
    [`inferModule`](#inferModule), producing [`TypeLookupTable`](TypeLookupTable#TypeLookupTable).
  - (When it's clear you need it) Get a [`Type`](Elm-TypeInference-Type#Type)
    for a given AST
    [`Node`](https://package.elm-lang.org/packages/stil4m/elm-syntax/latest/Elm-Syntax-Node#Node)'s
    [`Range`](https://package.elm-lang.org/packages/stil4m/elm-syntax/latest/Elm-Syntax-Range#Range) with [`get`](TypeLookupTable#get).

@docs dependencyEnv, DependencyEnvOutcome, DependencyEnv, Dependency

@docs project, Project

@docs inferModule, inferModules

@docs addFile, removeFile

-}

import Array
import Dict exposing (Dict)
import Elm.Docs
import Elm.Syntax.Declaration as Declaration exposing (Declaration)
import Elm.Syntax.Expression as Expression
import Elm.Syntax.Expression.Extra
import Elm.Syntax.File exposing (File)
import Elm.Syntax.File.Extra as FileExtra
import Elm.Syntax.FullModuleName as FullModuleName exposing (FullModuleName)
import Elm.Syntax.ModuleName exposing (ModuleName)
import Elm.Syntax.ModuleName.Extra as ModuleNameExtra
import Elm.Syntax.Node as Node exposing (Node(..))
import Elm.Syntax.Signature exposing (Signature)
import Elm.Syntax.Type as SyntaxType
import Elm.Syntax.TypeAlias
import Elm.Syntax.TypeAnnotation as TypeAnnotation
import Elm.Syntax.TypeAnnotation.Extra
import Elm.Type
import Elm.TypeInference.BindingGroup as BindingGroup
import Elm.TypeInference.Dependencies as Dependencies exposing (Dependencies)
import Elm.TypeInference.DependencySources as DependencySources
import Elm.TypeInference.Error exposing (Error, ErrorDetails(..))
import Elm.TypeInference.Error.Internal exposing (FromTypeAnnotationError)
import Elm.TypeInference.ImplicitImports as ImplicitImports
import Elm.TypeInference.Infer as Infer
import Elm.TypeInference.ModuleIds as ModuleIds exposing (ModuleId)
import Elm.TypeInference.ModuleIndex as ModuleIndex exposing (ModuleIndex)
import Elm.TypeInference.ModuleLookup as ModuleLookup
import Elm.TypeInference.SCC as SCC
import Elm.TypeInference.State as State exposing (GlobalKey, StateM)
import Elm.TypeInference.SubstitutionMap as SubstitutionMap
import Elm.TypeInference.Type exposing (PackageName, VarName)
import Elm.TypeInference.Type.Internal as TypeI exposing (MonoType(..), TypeResolver)
import Elm.TypeInference.TypeVar as TypeVar
import Elm.TypeInference.Unify exposing (TypeAlias)
import RangeLike
import Result.Extra
import Result.ExtraExtra
import Set exposing (Set)
import TypeLookupTable exposing (TypeLookupTable)
import TypeLookupTable.Internal



-- PROJECT INDEXING


{-| An indexed project: every file has been assigned a `ModuleId` and its
imports resolved, but nothing has been solved yet. Cheap to build.
-}
type Project
    = Project
        { currentPackage : Maybe PackageName
        , depEnv : DependencyEnv
        , moduleMapping : ModuleIds.Mapping
        , modulesById : Dict ModuleId ProjectModule
        , importedBy : Dict ModuleId (Set ModuleId)
        , acc : ProjectAcc
        }


{-| Analyze the import graph of the project source code, producing a [`Project`](#Project).
-}
project : Maybe PackageName -> DependencyEnv -> List File -> Result Error Project
project currentPackage depEnv files =
    -- Index files, assign ModuleIds, build the import graph.
    let
        (DependencyEnv dep) =
            depEnv

        ( modulesReversed, missingModuleName, moduleMapping ) =
            List.foldl
                (\file ( acc, accMissingModuleName, accModuleMapping ) ->
                    let
                        key : ModuleName
                        key =
                            FileExtra.moduleName file
                    in
                    if FullModuleName.moduleNameIsFull key then
                        let
                            ( index, newModuleMapping ) =
                                ModuleIndex.fromFile accModuleMapping file
                        in
                        ( { key = key, index = index, file = file } :: acc
                        , accMissingModuleName
                        , newModuleMapping
                        )

                    else
                        ( acc, True, accModuleMapping )
                )
                ( [], False, dep.moduleMapping )
                files
    in
    if missingModuleName then
        Err
            { moduleName = [ "<Missing>" ]
            , declarationNames = []
            , details = MissingModuleName
            }

    else
        let
            modulesById : Dict ModuleId ProjectModule
            modulesById =
                modulesReversed
                    |> List.foldl
                        (\m acc -> Dict.insert m.index.moduleId m acc)
                        Dict.empty

            importedBy : Dict ModuleId (Set ModuleId)
            importedBy =
                modulesReversed
                    |> List.foldl (\m acc -> addReverseEdges m.index acc) Dict.empty
        in
        Ok
            (Project
                { currentPackage = currentPackage
                , depEnv = depEnv
                , moduleMapping = moduleMapping
                , modulesById = modulesById
                , importedBy = importedBy
                , acc =
                    { tables = Dict.empty
                    , interfaces = Dict.empty
                    }
                }
            )


addReverseEdges : ModuleIndex -> Dict ModuleId (Set ModuleId) -> Dict ModuleId (Set ModuleId)
addReverseEdges index acc =
    index.imports
        |> List.foldl
            (\import_ innerAcc ->
                Dict.insert import_.moduleId
                    (Set.insert index.moduleId
                        (Maybe.withDefault Set.empty (Dict.get import_.moduleId innerAcc))
                    )
                    innerAcc
            )
            acc


firstPartyImportsOf : Dict ModuleId ProjectModule -> ModuleId -> List ModuleId
firstPartyImportsOf modulesById moduleId =
    case Dict.get moduleId modulesById of
        Nothing ->
            []

        Just m ->
            m.index.imports
                |> List.filterMap
                    (\import_ ->
                        if Dict.member import_.moduleId modulesById then
                            Just import_.moduleId

                        else
                            Nothing
                    )


{-| Every module reachable from `start`, `start` included.
-}
importClosure : (ModuleId -> List ModuleId) -> ModuleId -> Set ModuleId
importClosure edges start =
    importClosureHelp edges [ start ] Set.empty


importClosureHelp : (ModuleId -> List ModuleId) -> List ModuleId -> Set ModuleId -> Set ModuleId
importClosureHelp edges queue visited =
    case queue of
        [] ->
            visited

        node :: rest ->
            if Set.member node visited then
                importClosureHelp edges rest visited

            else
                importClosureHelp edges (edges node ++ rest) (Set.insert node visited)


inferNodes : Set ModuleId -> Project -> Project
inferNodes nodes (Project p) =
    let
        newAcc : ProjectAcc
        newAcc =
            SCC.setStronglyConnectedComponents nodes
                (\node -> firstPartyImportsOf p.modulesById node)
                |> List.foldl
                    (\list acc ->
                        List.foldl
                            (\id subAcc ->
                                if Dict.member id p.acc.interfaces then
                                    subAcc

                                else
                                    case Dict.get id p.modulesById of
                                        Just m ->
                                            inferOne p.currentPackage p.depEnv p.moduleMapping m subAcc

                                        Nothing ->
                                            subAcc
                            )
                            acc
                            list
                    )
                    p.acc
    in
    Project
        { acc = newAcc
        , currentPackage = p.currentPackage
        , depEnv = p.depEnv
        , moduleMapping = p.moduleMapping
        , modulesById = p.modulesById
        , importedBy = p.importedBy
        }


{-| Infer types in the given module.
-}
inferModule : ModuleName -> Project -> ( Result Error TypeLookupTable, Project )
inferModule moduleName ((Project p) as proj) =
    let
        target : Maybe ProjectModule
        target =
            FullModuleName.fromModuleName moduleName
                |> Maybe.andThen (\full -> ModuleIds.getId full p.moduleMapping)
                |> Maybe.andThen (\id -> Dict.get id p.modulesById)
    in
    case target of
        Nothing ->
            ( Err
                { moduleName = moduleName
                , declarationNames = []
                , details = ModuleNotFound
                }
            , proj
            )

        Just m ->
            let
                (Project newP) =
                    inferNodes
                        (importClosure (\modId -> firstPartyImportsOf p.modulesById modId) m.index.moduleId)
                        proj
            in
            ( case Dict.get m.key newP.acc.tables of
                Just result ->
                    result

                Nothing ->
                    Err
                        { moduleName = moduleName
                        , declarationNames = []
                        , details = ModuleNotFound
                        }
            , Project newP
            )


{-| Helper. Run [`inferModule`](#inferModules) for each of the given modules,
collecting successes and errors into separate `Dict`s.
-}
inferModules :
    List File
    -> Project
    ->
        ( { tables : Dict ModuleName TypeLookupTable
          , errors : Dict ModuleName Error
          }
        , Project
        )
inferModules files proj0 =
    let
        ( tables, errors, inferredProject ) =
            files
                |> List.foldl
                    (\file ( accTables, accErrors, proj ) ->
                        let
                            moduleName : ModuleName
                            moduleName =
                                FileExtra.moduleName file
                        in
                        case inferModule moduleName proj of
                            ( Ok table, newProj ) ->
                                ( Dict.insert moduleName table accTables
                                , accErrors
                                , newProj
                                )

                            ( Err err, newProj ) ->
                                ( accTables
                                , Dict.insert moduleName err accErrors
                                , newProj
                                )
                    )
                    ( Dict.empty
                    , Dict.empty
                    , proj0
                    )
    in
    ( { tables = tables, errors = errors }, inferredProject )



-- EDITING A PROJECT


{-| Remove each module (transitively) reachable from the supplied modules.
-}
invalidate : Dict ModuleId ProjectModule -> Set ModuleId -> Project -> Project
invalidate modulesById directlyAffected (Project p) =
    let
        affected : Set ModuleId
        affected =
            importClosureHelp
                (\id ->
                    case Dict.get id p.importedBy of
                        Just by ->
                            Set.toList by

                        Nothing ->
                            []
                )
                (Set.toList directlyAffected)
                Set.empty

        interfaces : Dict ModuleId ModuleInterface
        interfaces =
            Set.foldl Dict.remove p.acc.interfaces affected

        tables : Dict ModuleName (Result Error TypeLookupTable)
        tables =
            affected
                |> Set.foldl
                    (\id acc ->
                        case Dict.get id modulesById of
                            Just m ->
                                Dict.remove m.key acc

                            Nothing ->
                                acc
                    )
                    p.acc.tables
    in
    Project
        { acc =
            { tables = tables
            , interfaces = interfaces
            }
        , currentPackage = p.currentPackage
        , depEnv = p.depEnv
        , moduleMapping = p.moduleMapping
        , modulesById = p.modulesById
        , importedBy = p.importedBy
        }


{-| Make `Project` aware of a new or changed file.

**NOTE:** In addition to persisting the returned `Project`, you need to also
throw away the `TypeLookupTable` for this module that came from the old
`Project`. They have type inference data based on the old file's source code.
Instead run `inferModule` again on the new `Project` to get a new
`TypeLookupTable`.

-}
addFile : File -> Project -> Result Error Project
addFile file (Project p) =
    let
        moduleName : ModuleName
        moduleName =
            FileExtra.moduleName file
    in
    if FullModuleName.moduleNameIsFull moduleName then
        let
            ( newIndex, moduleMapping1 ) =
                ModuleIndex.fromFile p.moduleMapping file

            id : ModuleId
            id =
                newIndex.moduleId

            oldImportIds : Set ModuleId
            oldImportIds =
                case Dict.get id p.modulesById of
                    Just old ->
                        old.index.imports |> List.foldl (\im acc -> Set.insert im.moduleId acc) Set.empty

                    Nothing ->
                        Set.empty

            newImportIds : Set ModuleId
            newImportIds =
                newIndex.imports |> List.foldl (\im acc -> Set.insert im.moduleId acc) Set.empty

            importedBy1 : Dict ModuleId (Set ModuleId)
            importedBy1 =
                oldImportIds
                    |> Set.foldl
                        (\importId acc ->
                            if Set.member importId newImportIds then
                                acc

                            else
                                case Dict.get importId acc of
                                    Nothing ->
                                        acc

                                    Just by ->
                                        Dict.insert importId
                                            (by |> Set.remove id)
                                            acc
                        )
                        p.importedBy

            importedBy2 : Dict ModuleId (Set ModuleId)
            importedBy2 =
                newImportIds
                    |> Set.foldl
                        (\importId acc ->
                            if Set.member importId oldImportIds then
                                acc

                            else
                                Dict.insert importId
                                    (case Dict.get importId acc of
                                        Nothing ->
                                            Set.singleton id

                                        Just importers ->
                                            Set.insert id importers
                                    )
                                    acc
                        )
                        importedBy1

            modulesById1 : Dict ModuleId ProjectModule
            modulesById1 =
                Dict.insert id
                    { key = moduleName
                    , index = newIndex
                    , file = file
                    }
                    p.modulesById
        in
        Ok
            (invalidate modulesById1
                (Set.singleton id)
                (Project
                    { moduleMapping = moduleMapping1
                    , modulesById = modulesById1
                    , importedBy = importedBy2
                    , acc = p.acc
                    , currentPackage = p.currentPackage
                    , depEnv = p.depEnv
                    }
                )
            )

    else
        -- moduleName is not full
        Err
            { moduleName = moduleName
            , declarationNames = []
            , details = MissingModuleName
            }


{-| Remove a module from a `Project`.

**NOTE:** In addition to persisting the returned `Project`, you need to also
throw away the `TypeLookupTable` for this module that came from the old
`Project`.

-}
removeFile : ModuleName -> Project -> Project
removeFile moduleName ((Project p) as proj) =
    case
        FullModuleName.fromModuleName moduleName
            |> Maybe.andThen (\full -> ModuleIds.getId full p.moduleMapping)
            |> Maybe.andThen (\id -> Dict.get id p.modulesById |> Maybe.map (\mod -> ( id, mod )))
    of
        Nothing ->
            proj

        Just ( id, m ) ->
            let
                modulesById1 : Dict ModuleId ProjectModule
                modulesById1 =
                    Dict.remove id p.modulesById

                importedBy1 : Dict ModuleId (Set ModuleId)
                importedBy1 =
                    m.index.imports
                        |> List.foldl
                            (\import_ acc ->
                                case Dict.get import_.moduleId acc of
                                    Nothing ->
                                        acc

                                    Just by ->
                                        Dict.insert import_.moduleId (by |> Set.remove id) acc
                            )
                            p.importedBy
            in
            invalidate p.modulesById
                (Set.singleton id)
                (Project
                    { modulesById = modulesById1
                    , importedBy = importedBy1
                    , acc = p.acc
                    , depEnv = p.depEnv
                    , currentPackage = p.currentPackage
                    , moduleMapping = p.moduleMapping
                    }
                )



-- DEPENDENCIES


{-| Input to [`dependencyEnv`](#dependencyEnv).

A dependency package with its type information, parsed from the dependency's
`elm.json` (via
[`Elm.Project.decoder`](https://package.elm-lang.org/packages/elm/project-metadata-utils/latest/Elm-Project#decoder))
and `docs.json` (via `elm/project-metadata-utils`
[`Elm.Docs.decoder`](https://package.elm-lang.org/packages/elm/project-metadata-utils/latest/Elm-Docs#decoder)):

  - **name:** the package identifier (e.g. `"elm/html"`).
  - **dependencies:** names of the package's _immediate_ `elm.json` dependencies (eg. `"elm/virtual-dom"`).
  - **modules:** the decoded `docs.json` modules.

-}
type alias Dependency =
    { name : PackageName
    , dependencies : List PackageName
    , modules : List Elm.Docs.Module
    }


{-| Data parsed from dependencies' `docs.json` files.

This cache doesn't change as user's project code changes - only invalidate it
and [`Project`](#Project) when `elm.json` changes.

-}
type DependencyEnv
    = DependencyEnv
        { globalEnv : Dict GlobalKey TypeI.Type
        , typeAliases : Dict GlobalKey TypeAlias
        , index : ModuleLookup.Index
        , moduleMapping : ModuleIds.Mapping
        }


{-| Possible outcomes of running [`dependencyEnv`](#dependencyEnv).

An example `NeedPackageSources`:

    Dict.fromList
        [ ( "example/css", [ "src/Css/Internal.elm" ] ) ]

-}
type DependencyEnvOutcome
    = Ready DependencyEnv
    | NeedPackageSources (Dict PackageName (List String))
    | Failed Error


{-| Build a [`DependencyEnv`](#DependencyEnv).

Initially you can run with `sourcesToResolveAmbiguity = Dict.empty`. If you get
`NeedPackageSources` back, read and parse those Elm files from the dependencies
in your `ELM_HOME` (usually `~/.elm`) and supply them in
`sourcesToResolveAmbiguity` in the next call.

-}
dependencyEnv :
    { directDependencies : List PackageName
    , allDependencies : List Dependency
    , sourcesToResolveAmbiguity : Dict PackageName (List File)
    }
    -> DependencyEnvOutcome
dependencyEnv { directDependencies, allDependencies, sourcesToResolveAmbiguity } =
    let
        deps : Dependencies
        deps =
            Dependencies.fromList allDependencies

        reachable : Set PackageName
        reachable =
            reachablePackages deps directDependencies

        needed : Dict PackageName (List String)
        needed =
            DependencySources.neededSources deps sourcesToResolveAmbiguity
                |> List.foldl
                    (\( pkg, names ) acc ->
                        if Set.member pkg reachable then
                            Dict.insert pkg names acc

                        else
                            acc
                    )
                    Dict.empty
    in
    if Dict.isEmpty needed then
        let
            directVisibleDeps : Dependencies
            directVisibleDeps =
                allDependencies
                    |> List.foldl
                        (\pkg acc ->
                            if List.member pkg.name directDependencies then
                                Dict.insert pkg.name pkg acc

                            else
                                acc
                        )
                        Dict.empty

            moduleMapping0 : ModuleIds.Mapping
            moduleMapping0 =
                allDependencies
                    |> List.foldl
                        (\pkg acrossDependencies ->
                            List.foldl
                                (\m acc ->
                                    ModuleIds.intern (FullModuleName.fromDotted m.name) acc |> Tuple.second
                                )
                                acrossDependencies
                                pkg.modules
                        )
                        (List.foldl
                            (\name acc ->
                                ModuleIds.intern (FullModuleName.fromDotted name) acc |> Tuple.second
                            )
                            ModuleIds.empty
                            (DependencySources.referencedModules deps)
                        )

            ( depIndex, moduleMapping1 ) =
                ModuleLookup.buildIndex moduleMapping0 directVisibleDeps

            moduleMapping2 : ModuleIds.Mapping
            moduleMapping2 =
                deps
                    |> Dict.foldl
                        (\_ item accAcrossDeps ->
                            item.modules
                                |> List.foldl
                                    (\mod acc ->
                                        ModuleIds.intern (FullModuleName.fromDotted mod.name) acc
                                            |> Tuple.second
                                    )
                                    accAcrossDeps
                        )
                        moduleMapping1

            baseEnv :
                Result
                    Error
                    ( { globalEnv : Dict GlobalKey TypeI.Type
                      , typeAliases : Dict GlobalKey TypeAlias
                      , index : ModuleLookup.Index
                      }
                    , ModuleIds.Mapping
                    )
            baseEnv =
                (State.do
                    (SCC.dictKeysStronglyConnectedComponents deps
                        (\pkgName ->
                            case Dict.get pkgName deps of
                                Nothing ->
                                    []

                                Just pkg ->
                                    pkg.dependencies
                        )
                        |> State.concatAndFoldl
                            (\pkgName ( accTypeAliases, accModuleMapping ) ->
                                case Dict.get pkgName deps of
                                    Just pkg ->
                                        dependencyPackageEnv pkgName pkg deps sourcesToResolveAmbiguity accModuleMapping accTypeAliases

                                    Nothing ->
                                        State.pure ( accTypeAliases, accModuleMapping )
                            )
                            ( Dict.empty, moduleMapping2 )
                    )
                 <| \( depAliases, moduleMapping3 ) ->
                 State.do State.getGlobalEnv <| \globalEnv ->
                 State.pure <|
                     ( { globalEnv = globalEnv
                       , typeAliases = depAliases
                       , index = depIndex
                       }
                     , moduleMapping3
                     )
                )
                    |> State.run State.empty
                    |> Tuple.first
        in
        case baseEnv of
            Err err ->
                Failed err

            Ok ( env, moduleMapping3 ) ->
                Ready
                    (DependencyEnv
                        { globalEnv = env.globalEnv
                        , index = env.index
                        , typeAliases = env.typeAliases
                        , moduleMapping = moduleMapping3
                        }
                    )

    else
        NeedPackageSources needed


type alias TypeAliases =
    Dict ( ModuleId, PackageName, VarName ) TypeAlias


dependencyPackageEnv :
    String
    -> Dependencies.DependencyPackage
    -> Dependencies
    -> Dict String (List File)
    -> ModuleIds.Mapping
    -> TypeAliases
    -> StateM ( TypeAliases, ModuleIds.Mapping )
dependencyPackageEnv pkgName pkg deps sourcesToResolveAmbiguity accModuleMapping accTypeAliases =
    let
        addModule : PackageName -> Elm.Docs.Module -> Dict String (List PackageName) -> Dict String (List PackageName)
        addModule modulePkgName mod acc =
            Dict.insert mod.name
                (case Dict.get mod.name acc of
                    Nothing ->
                        [ modulePkgName ]

                    Just byMod ->
                        byMod ++ [ modulePkgName ]
                )
                acc

        dependencyOwnersByModule : Dict String (List PackageName)
        dependencyOwnersByModule =
            pkg.dependencies
                |> List.foldl
                    (\searchPkgName accAcrossPks ->
                        case Dict.get searchPkgName deps of
                            Just searchPkg ->
                                List.foldl (\mod acc -> addModule searchPkgName mod acc) accAcrossPks searchPkg.modules

                            Nothing ->
                                accAcrossPks
                    )
                    (List.foldl (\mod acc -> addModule pkgName mod acc) Dict.empty pkg.modules)

        moduleNameOriginDependencyResolver : Dependencies.Resolver
        moduleNameOriginDependencyResolver moduleNameStr =
            if String.isEmpty moduleNameStr then
                -- Impossible in principle (Elm compiler generates docs.json with fully qualified types).
                -- Possible in practice (if somebody hand-crafts a docs.json file).
                Err
                    (AmbiguousModuleOwner
                        { moduleName = moduleNameStr
                        , possiblePackages = []
                        }
                    )

            else
                case ModuleIds.getIdByDotted moduleNameStr accModuleMapping of
                    Nothing ->
                        -- Impossible if we pre-intern docs modules properly.
                        -- Possible if we have a bug.
                        Err
                            (AmbiguousModuleOwner
                                { moduleName = moduleNameStr
                                , possiblePackages = []
                                }
                            )

                    Just moduleId ->
                        case Dict.get moduleNameStr dependencyOwnersByModule |> Maybe.withDefault [] of
                            [] ->
                                Ok ( pkgName, moduleId )

                            [ owner ] ->
                                Ok ( owner, moduleId )

                            matches ->
                                Err <|
                                    AmbiguousModuleOwner
                                        { moduleName = moduleNameStr
                                        , possiblePackages = matches
                                        }

        pkgDocsModulesDict : Dict String Elm.Docs.Module
        pkgDocsModulesDict =
            pkg.modules
                |> List.foldl
                    (\pkgModule acc ->
                        Dict.insert pkgModule.name pkgModule acc
                    )
                    Dict.empty

        sourceFiles : List File
        sourceFiles =
            Dict.get pkgName sourcesToResolveAmbiguity |> Maybe.withDefault []

        ( sourceFileModuleIndexByModuleId, sourceFileAndModuleIndexByName, moduleMapping1 ) =
            sourceFiles
                |> List.foldl
                    (\file ( acc, accSourceFileByName, acrossSourceFilesModuleMapping ) ->
                        let
                            ( moduleIndex, newModuleMapping ) =
                                ModuleIndex.fromFile acrossSourceFilesModuleMapping file
                        in
                        ( Dict.insert moduleIndex.moduleId moduleIndex acc
                        , Dict.insert (moduleIndex.moduleName |> FullModuleName.toString)
                            ( file, moduleIndex )
                            accSourceFileByName
                        , newModuleMapping
                        )
                    )
                    ( Dict.empty, Dict.empty, accModuleMapping )

        moduleOriginLookupIndex : ModuleLookup.Index
        moduleOriginLookupIndex =
            deps
                |> Dict.filter
                    (\name _ ->
                        name == pkgName || List.member name pkg.dependencies
                    )
                |> ModuleLookup.buildIndex moduleMapping1
                |> Tuple.first
    in
    SCC.stronglyConnectedComponents
        (Dict.foldl
            (\sourceFileModuleNameString _ acc ->
                if Dict.member sourceFileModuleNameString pkgDocsModulesDict then
                    acc

                else
                    sourceFileModuleNameString :: acc
            )
            (Dict.keys pkgDocsModulesDict)
            sourceFileAndModuleIndexByName
        )
        (\pkgModuleName ->
            case Dict.get pkgModuleName pkgDocsModulesDict of
                Nothing ->
                    case Dict.get pkgModuleName sourceFileAndModuleIndexByName of
                        Nothing ->
                            []

                        Just ( _, moduleIndex ) ->
                            List.map (\import_ -> import_.dottedModuleName) moduleIndex.imports

                Just pkgModule ->
                    Dependencies.addDocsModuleRefNamesToList pkgModule []
        )
        |> State.concatAndFoldl
            (\modName acrossModulesTypeAliases ->
                case Dict.get modName pkgDocsModulesDict of
                    Just mod ->
                        case ModuleIds.getIdByDotted modName moduleMapping1 of
                            Nothing ->
                                -- Impossible if we intern modules properly.
                                -- Possible if we have a bug.
                                State.error
                                    { moduleName = ModuleNameExtra.fromDotted modName
                                    , declarationNames = []
                                    , details =
                                        AmbiguousModuleOwner
                                            { moduleName = modName
                                            , possiblePackages = []
                                            }
                                    }

                            Just moduleId ->
                                dependencyPackageModuleEnv
                                    pkgName
                                    moduleId
                                    modName
                                    mod
                                    moduleMapping1
                                    moduleNameOriginDependencyResolver
                                    moduleOriginLookupIndex
                                    sourceFileAndModuleIndexByName
                                    sourceFileModuleIndexByModuleId
                                    acrossModulesTypeAliases

                    Nothing ->
                        case Dict.get modName sourceFileAndModuleIndexByName of
                            Just ( sourceFile, thisModule ) ->
                                dependencyPackageModuleSourceTypeAliases
                                    pkgName
                                    moduleMapping1
                                    moduleOriginLookupIndex
                                    sourceFileModuleIndexByModuleId
                                    thisModule
                                    sourceFile
                                    acrossModulesTypeAliases
                                    |> State.fromResult

                            Nothing ->
                                State.pure acrossModulesTypeAliases
            )
            accTypeAliases
        |> State.map (\aliases -> ( aliases, moduleMapping1 ))


dependencyPackageModuleEnv :
    PackageName
    -> ModuleId
    -> String
    -> Elm.Docs.Module
    -> ModuleIds.Mapping
    -> Dependencies.Resolver
    -> ModuleLookup.Index
    -> Dict String ( File, ModuleIndex )
    -> Dict ModuleId ModuleIndex
    -> TypeAliases
    -> State.State
    -> ( Result Error TypeAliases, State.State )
dependencyPackageModuleEnv pkgName moduleId modName docsModule moduleMapping1 moduleNameOriginDependencyResolver moduleOriginLookupIndex sourceFileAndModuleIndexByName sourceFileModuleIndexByModuleId acrossModulesTypeAliases =
    let
        addBinding :
            TypeAliases
            -> VarName
            -> Elm.Type.Type
            -> StateM ()
        addBinding typeAliases name tipe =
            case fromDocsType moduleNameOriginDependencyResolver typeAliases tipe of
                Err details ->
                    State.error
                        { moduleName = ModuleNameExtra.fromDotted docsModule.name
                        , declarationNames = []
                        , details = details
                        }

                Ok monoType ->
                    State.addGlobalBinding ( moduleId, pkgName, name ) (TypeI.closeOver monoType)
    in
    State.do
        (case Dict.get modName sourceFileAndModuleIndexByName of
            Just ( sourceFile, thisModule ) ->
                -- TODO why do we not need to add global bindings for the public ones
                -- while non-source docs modules do?
                -- My(lue-bird) current assumption: Adding any type aliases to global bindings is
                -- always unnecessary
                dependencyPackageModuleSourceTypeAliases
                    pkgName
                    moduleMapping1
                    moduleOriginLookupIndex
                    sourceFileModuleIndexByModuleId
                    thisModule
                    sourceFile
                    acrossModulesTypeAliases
                    |> State.fromResult

            Nothing ->
                let
                    docsAliasDict : Dict String Elm.Docs.Alias
                    docsAliasDict =
                        docsModule.aliases
                            |> List.foldl (\alias -> Dict.insert alias.name alias)
                                Dict.empty
                in
                SCC.dictKeysStronglyConnectedComponents docsAliasDict
                    (\aliasName ->
                        case Dict.get aliasName docsAliasDict of
                            Nothing ->
                                []

                            Just alias ->
                                Dependencies.addDocsTypeRefsWithSameModuleNameToList modName alias.tipe []
                    )
                    |> State.concatAndFoldl
                        (\typeAliasName acc ->
                            case Dict.get typeAliasName docsAliasDict of
                                Nothing ->
                                    State.pure acc

                                Just typeAlias ->
                                    docsAliasAddToTypeAliasesAndRegisterConstructor
                                        pkgName
                                        moduleId
                                        docsModule.name
                                        moduleNameOriginDependencyResolver
                                        typeAlias
                                        acc
                        )
                        acrossModulesTypeAliases
        )
    <| \typeAliasesIncludingMod ->
    State.do (State.traverseUnit (\v -> addBinding typeAliasesIncludingMod v.name v.tipe) docsModule.values) <| \() ->
    State.do (State.traverseUnit (\b -> addBinding typeAliasesIncludingMod b.name b.tipe) docsModule.binops) <| \() ->
    State.do
        (State.traverseUnit
            (\union ->
                registerDocsUnion pkgName moduleId docsModule.name moduleNameOriginDependencyResolver typeAliasesIncludingMod union
            )
            docsModule.unions
        )
    <| \() ->
    if ModuleIds.equal moduleId ModuleIds.basicsId then
        -- overwrite types of True and False, the only 2 variants where the result is not a UserDefinedType
        State.do
            (State.addGlobalBinding
                ( ModuleIds.basicsId, ImplicitImports.elmCorePackage, "True" )
                (TypeI.closeOver TypeI.Bool)
            )
        <| \() ->
        State.do
            (State.addGlobalBinding
                ( ModuleIds.basicsId, ImplicitImports.elmCorePackage, "False" )
                (TypeI.closeOver TypeI.Bool)
            )
        <| \() ->
        State.pure typeAliasesIncludingMod

    else
        State.pure typeAliasesIncludingMod


dependencyPackageModuleSourceTypeAliases :
    String
    -> ModuleIds.Mapping
    -> ModuleLookup.Index
    -> Dict ModuleId ModuleIndex
    -> ModuleIndex
    -> File
    -> TypeAliases
    -> Result Error TypeAliases
dependencyPackageModuleSourceTypeAliases pkgName moduleMapping1 moduleOriginLookupIndex sourceFileModuleIndexByModuleId thisModule sourceFile acrossModulesTypeAliases =
    let
        typeOriginResolver : TypeI.TypeResolver
        typeOriginResolver qualifier name =
            ModuleLookup.typeResolverFor moduleMapping1 moduleOriginLookupIndex sourceFileModuleIndexByModuleId thisModule qualifier name
                |> Result.map
                    (\( owner, lookupModuleId ) ->
                        ( if owner == "" then
                            pkgName

                          else
                            owner
                        , lookupModuleId
                        )
                    )

        fileTypeAliases : Dict String Elm.Syntax.TypeAlias.TypeAlias
        fileTypeAliases =
            sourceFile.declarations
                |> List.foldl
                    (\node accFileTypeAliases ->
                        case Node.value node of
                            Declaration.AliasDeclaration alias_ ->
                                Dict.insert (Node.value alias_.name) alias_ accFileTypeAliases

                            _ ->
                                accFileTypeAliases
                    )
                    Dict.empty
    in
    SCC.dictKeysStronglyConnectedComponents fileTypeAliases
        (\node ->
            case Dict.get node fileTypeAliases of
                Nothing ->
                    []

                Just alias_ ->
                    Elm.Syntax.TypeAnnotation.Extra.referencesToTypesFromModuleId
                        typeOriginResolver
                        thisModule.moduleId
                        (Node.value alias_.typeAnnotation)
        )
        |> Result.ExtraExtra.concatAndFoldl
            (\node dict ->
                case Dict.get node fileTypeAliases of
                    Just alias_ ->
                        TypeI.fromTypeAnnotation typeOriginResolver
                            dict
                            (Node.value alias_.typeAnnotation)
                            |> Result.mapError
                                (\err ->
                                    { moduleName = FullModuleName.toModuleName thisModule.moduleName
                                    , declarationNames = [ Node.value alias_.name ]
                                    , details = TypeI.fromTypeAnnotationError err
                                    }
                                )
                            |> Result.map
                                (\body ->
                                    Dict.insert
                                        ( thisModule.moduleId, pkgName, Node.value alias_.name )
                                        { args = List.map (\(Node.Node _ generic) -> TypeVar.parse generic) alias_.generics
                                        , type_ = body
                                        }
                                        dict
                                )

                    Nothing ->
                        Ok dict
            )
            acrossModulesTypeAliases


registerDocsUnion :
    PackageName
    -> ModuleId
    -> String
    -> Dependencies.Resolver
    -> TypeAliases
    -> Elm.Docs.Union
    -> StateM ()
registerDocsUnion pkgName moduleId dottedModuleName resolver typeAliases union =
    let
        toError : ErrorDetails -> Error
        toError details =
            { moduleName = ModuleNameExtra.fromDotted dottedModuleName
            , declarationNames = []
            , details = details
            }

        args : List MonoType
        args =
            union.args |> List.map (\argName -> TypeVar (TypeVar.parse argName))

        resultType : MonoType
        resultType =
            UserDefinedType
                { package = pkgName
                , moduleId = moduleId
                , name = union.name
                , args = args
                }
    in
    union.tags
        |> State.traverseUnit
            (\( ctorName, argTypeStrings ) ->
                State.do
                    (State.fromResult
                        (Result.mapError toError
                            (Result.Extra.combineMap
                                (\argDocsType -> fromDocsType resolver typeAliases argDocsType)
                                argTypeStrings
                            )
                        )
                    )
                <| \argTypes ->
                let
                    ctorType : MonoType
                    ctorType =
                        argTypes
                            |> List.foldr (\argT acc -> Function { from = argT, to = acc }) resultType
                in
                State.addGlobalBinding ( moduleId, pkgName, ctorName ) (TypeI.closeOver ctorType)
            )


{-| A record type definition gets a constructor function as well
-}
docsAliasAddToTypeAliasesAndRegisterConstructor :
    PackageName
    -> ModuleId
    -> String
    -> Dependencies.Resolver
    -> Elm.Docs.Alias
    -> TypeAliases
    -> StateM TypeAliases
docsAliasAddToTypeAliasesAndRegisterConstructor pkgName moduleId dottedModuleName resolver docsAlias typeAliases =
    case fromDocsType resolver typeAliases docsAlias.tipe of
        Err details ->
            State.error
                { moduleName = ModuleNameExtra.fromDotted dottedModuleName
                , declarationNames = []
                , details = details
                }

        Ok aliasMono ->
            let
                typeAliasesIncludingThisOne : TypeAliases
                typeAliasesIncludingThisOne =
                    Dict.insert ( moduleId, pkgName, docsAlias.name )
                        { args = List.map TypeVar.parse docsAlias.args, type_ = aliasMono }
                        typeAliases
            in
            case docsAlias.tipe of
                Elm.Type.Record fields Nothing ->
                    case aliasMono of
                        TypeI.Record monoFields ->
                            let
                                ctorType : MonoType
                                ctorType =
                                    List.foldr
                                        (\( fieldName, _ ) acc ->
                                            case Dict.get fieldName monoFields of
                                                Just fieldT ->
                                                    Function { from = fieldT, to = acc }

                                                Nothing ->
                                                    -- impossible. If this is reached there is a bug in fromDocsType
                                                    acc
                                        )
                                        aliasMono
                                        fields
                            in
                            State.addGlobalBinding ( moduleId, pkgName, docsAlias.name ) (TypeI.closeOver ctorType)
                                |> State.map (\() -> typeAliasesIncludingThisOne)

                        _ ->
                            -- impossible. If this is reached there is a bug in fromDocsType
                            State.pure typeAliasesIncludingThisOne

                _ ->
                    State.pure typeAliasesIncludingThisOne


fromDocsType :
    Dependencies.Resolver
    -> TypeAliases
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

        Elm.Type.Tuple parts ->
            case parts of
                [] ->
                    Ok Unit

                [ a, b ] ->
                    Result.map2 Tuple2
                        (fromDocsType resolver typeAliases a)
                        (fromDocsType resolver typeAliases b)

                [ a, b, c ] ->
                    Result.map3 Tuple3
                        (fromDocsType resolver typeAliases a)
                        (fromDocsType resolver typeAliases b)
                        (fromDocsType resolver typeAliases c)

                _ ->
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

        Elm.Type.Record fields extended ->
            dictFromDocsFields resolver typeAliases fields
                |> Result.map
                    (case extended of
                        Nothing ->
                            Record

                        Just rowVar ->
                            \resolvedFields ->
                                ExtensibleRecord
                                    { extensionTypevar = TypeVar (TypeVar.parse rowVar)
                                    , fields = resolvedFields
                                    }
                    )


dictFromDocsFields :
    Dependencies.Resolver
    -> TypeAliases
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


reachablePackages : Dependencies -> List PackageName -> Set PackageName
reachablePackages deps roots =
    reachablePackagesHelp deps roots Set.empty


reachablePackagesHelp : Dependencies -> List PackageName -> Set PackageName -> Set PackageName
reachablePackagesHelp deps queue seen =
    case queue of
        [] ->
            seen

        name :: rest ->
            if Set.member name seen then
                reachablePackagesHelp deps rest seen

            else
                case Dict.get name deps of
                    Nothing ->
                        reachablePackagesHelp deps rest (Set.insert name seen)

                    Just pkg ->
                        reachablePackagesHelp deps (rest ++ pkg.dependencies) (Set.insert name seen)



-- PER-MODULE INFERENCE (internal)


{-| What one module contributes to the modules that import it.
-}
type alias ModuleInterface =
    { moduleIndex : ModuleIndex
    , values : Dict VarName TypeI.Type
    , typeAliases : Dict GlobalKey TypeAlias
    }


type alias ProjectModule =
    { key : ModuleName
    , index : ModuleIndex
    , file : File
    }


type alias ProjectAcc =
    { tables : Dict ModuleName (Result Error TypeLookupTable)
    , interfaces : Dict ModuleId ModuleInterface
    }


inferOne : Maybe PackageName -> DependencyEnv -> ModuleIds.Mapping -> ProjectModule -> ProjectAcc -> ProjectAcc
inferOne currentPackage depEnv moduleMapping m acc =
    let
        imported : Dict ModuleId ModuleInterface
        imported =
            m.index.imports
                |> List.foldl
                    (\import_ inner ->
                        case Dict.get import_.moduleId acc.interfaces of
                            Just interface ->
                                Dict.insert import_.moduleId interface inner

                            Nothing ->
                                inner
                    )
                    Dict.empty
    in
    case inferModule_ currentPackage depEnv moduleMapping imported m.index m.file of
        Ok { table, interface } ->
            { tables = Dict.insert m.key (Ok table) acc.tables
            , interfaces = Dict.insert m.index.moduleId interface acc.interfaces
            }

        Err err ->
            { tables = Dict.insert m.key (Err err) acc.tables
            , interfaces =
                Dict.insert m.index.moduleId
                    { moduleIndex = m.index
                    , values = Dict.empty
                    , typeAliases = Dict.empty
                    }
                    acc.interfaces
            }



-- THE CORE


{-| Everything a single module's inference needs, derived once from the
`DependencyEnv` and the imported interfaces.
-}
type alias ModuleCtx =
    { thisIndex : ModuleIndex
    , modules : Dict ModuleId ModuleIndex
    , resolver : TypeResolver
    , index : ModuleLookup.Index
    , moduleMapping : ModuleIds.Mapping
    , -- what this module passes on to its own importers
      inheritedAliases : Dict GlobalKey TypeAlias
    , depTypeAliases : Dict GlobalKey TypeAlias
    , globalEnv : Dict GlobalKey TypeI.Type
    , allowKernel : Bool
    }


allowsKernel : Maybe PackageName -> Bool
allowsKernel currentPackage =
    case currentPackage of
        Nothing ->
            True

        Just name ->
            String.startsWith "elm/" name
                || String.startsWith "elm-explorations/" name


moduleCtx : Maybe PackageName -> DependencyEnv -> ModuleIds.Mapping -> Dict ModuleId ModuleInterface -> ModuleIndex -> ModuleCtx
moduleCtx currentPackage (DependencyEnv depEnv) moduleMapping importedInterfaces thisIndex =
    let
        modules : Dict ModuleId ModuleIndex
        modules =
            importedInterfaces
                |> Dict.map (\_ interface -> interface.moduleIndex)
                |> Dict.insert thisIndex.moduleId thisIndex

        imported :
            { inheritedAliases : Dict GlobalKey TypeAlias
            , globalEnv : Dict GlobalKey TypeI.Type
            }
        imported =
            Dict.foldl
                (\moduleId interface acc ->
                    { inheritedAliases = Dict.union interface.typeAliases acc.inheritedAliases
                    , globalEnv =
                        Dict.foldl
                            (\name scheme inner -> Dict.insert ( moduleId, "", name ) scheme inner)
                            acc.globalEnv
                            interface.values
                    }
                )
                { inheritedAliases = Dict.empty
                , globalEnv = depEnv.globalEnv
                }
                importedInterfaces
    in
    { thisIndex = thisIndex
    , modules = modules
    , resolver = ModuleLookup.typeResolverFor moduleMapping depEnv.index modules thisIndex
    , index = depEnv.index
    , moduleMapping = moduleMapping
    , inheritedAliases = imported.inheritedAliases
    , depTypeAliases = depEnv.typeAliases
    , globalEnv = imported.globalEnv
    , allowKernel = allowsKernel currentPackage
    }


inferModule_ :
    Maybe PackageName
    -> DependencyEnv
    -> ModuleIds.Mapping
    -> Dict ModuleId ModuleInterface
    -> ModuleIndex
    -> File
    -> Result Error { table : TypeLookupTable, interface : ModuleInterface }
inferModule_ currentPackage depEnv moduleMapping importedInterfaces thisIndex file =
    let
        ctx : ModuleCtx
        ctx =
            moduleCtx currentPackage depEnv moduleMapping importedInterfaces thisIndex
    in
    (State.do (gatherTypeAliases ctx file) <| \typeAliases ->
    State.do (registerConstructorsAndPorts ctx typeAliases file) <| \() ->
    State.do (registerEffectMagic ctx) <| \() ->
    State.do (solveModule ctx typeAliases file) <| \() ->
    moduleResult ctx file typeAliases
    )
        |> State.run (State.init ctx.globalEnv)
        |> Tuple.first


moduleResult :
    ModuleCtx
    -> File
    -> Dict GlobalKey TypeAlias
    ->
        StateM
            { table : TypeLookupTable
            , interface : ModuleInterface
            }
moduleResult ctx file typeAliases =
    State.do State.getNodeIds <| \nodeIds ->
    State.do State.getSubst <| \substitutionMap ->
    State.do State.getGlobalEnv <| \globalEnv ->
    let
        exposedValues : Dict VarName TypeI.Type
        exposedValues =
            ctx.thisIndex.exposedValues
                |> Set.foldl
                    (\name acc ->
                        case Dict.get ( ctx.thisIndex.moduleId, "", name ) globalEnv of
                            Just scheme ->
                                Dict.insert name scheme acc

                            Nothing ->
                                acc
                    )
                    Dict.empty

        annotationFor : Dict TypeI.Id TypeI.MonoType
        annotationFor =
            file.declarations
                |> List.foldl
                    (\(Node declRange decl) acc ->
                        case decl of
                            Declaration.FunctionDeclaration fn ->
                                case fn.signature of
                                    Nothing ->
                                        acc

                                    Just (Node _ sigNode) ->
                                        case Dict.get (RangeLike.fromRange declRange) nodeIds of
                                            Nothing ->
                                                acc

                                            Just declId ->
                                                case TypeI.fromTypeAnnotation ctx.resolver typeAliases (Node.value sigNode.typeAnnotation) of
                                                    Err _ ->
                                                        acc

                                                    Ok annoMono ->
                                                        Dict.insert declId annoMono acc

                            _ ->
                                acc
                    )
                    Dict.empty
    in
    State.pure
        { table =
            TypeLookupTable.Internal.TLT
                { nodeIds = nodeIds
                , subst = SubstitutionMap.forLookup substitutionMap
                , moduleMapping = ctx.moduleMapping
                , cache = Array.empty
                , pool = Dict.empty
                , annotationFor = annotationFor
                }
        , interface =
            { moduleIndex = ctx.thisIndex
            , values = exposedValues
            , typeAliases =
                -- TODO this is quiite scuffed.
                -- It may be nicer (and faster) to instead pass
                -- outgoing and depTypeAliases separately to TypeI.fromTypeAnnotation
                typeAliases
                    |> Dict.filter
                        (\( moduleId, _, _ ) _ ->
                            ModuleIds.equal moduleId ctx.thisIndex.moduleId
                        )
            }
        }



-- SOLVING ONE MODULE'S TOP-LEVEL DECLARATIONS


solveModule :
    ModuleCtx
    -> Dict GlobalKey TypeAlias
    -> File
    -> StateM ()
solveModule ctx typeAliases file =
    let
        topLevelFunctions : Dict VarName ( Node Declaration, Expression.Function )
        topLevelFunctions =
            file.declarations
                |> List.foldl
                    (\((Node _ decl) as declNode) byName ->
                        case decl of
                            Declaration.FunctionDeclaration fn ->
                                Dict.insert (Elm.Syntax.Expression.Extra.functionName fn)
                                    ( declNode, fn )
                                    byName

                            _ ->
                                byName
                    )
                    Dict.empty

        edges : VarName -> List VarName
        edges key =
            case Dict.get key topLevelFunctions of
                Nothing ->
                    []

                Just ( _, fn ) ->
                    Elm.Syntax.Expression.Extra.referencedNames (Node.value (Node.value fn.declaration).expression)
                        -- Resolve operator aliases to the underlying functions
                        |> List.filterMap
                            (\( maybeModuleName, varName ) ->
                                case ModuleLookup.moduleOfVar ctx.moduleMapping ctx.index ctx.modules ctx.thisIndex (Maybe.andThen FullModuleName.fromModuleName maybeModuleName) varName of
                                    Ok (Just ( "", moduleId )) ->
                                        let
                                            ( resolvedModule, resolvedName ) =
                                                case
                                                    ModuleLookup.resolveOperatorFunction ctx.moduleMapping ctx.modules moduleId varName
                                                        |> Result.withDefault Nothing
                                                of
                                                    Just resolved ->
                                                        resolved

                                                    Nothing ->
                                                        ( moduleId, varName )
                                        in
                                        -- Only this module's own declarations
                                        -- are being ordered here; everything
                                        -- else is already in `globalEnv`.
                                        if ModuleIds.equal resolvedModule ctx.thisIndex.moduleId && Dict.member resolvedName topLevelFunctions then
                                            Just resolvedName

                                        else
                                            Nothing

                                    _ ->
                                        Nothing
                            )

        sccs : List (List VarName)
        sccs =
            SCC.dictKeysStronglyConnectedComponents topLevelFunctions edges

        inferCtx : Infer.Ctx
        inferCtx =
            { modules = ctx.modules
            , thisModule = ctx.thisIndex
            , typeAliases = typeAliases
            , index = ctx.index
            , allowKernel = ctx.allowKernel
            , moduleMapping = ctx.moduleMapping
            }
    in
    sccs
        |> State.traverseUnit
            (\group ->
                group
                    |> State.foldl
                        (\key acc ->
                            case Dict.get key topLevelFunctions of
                                Just ( declNode, fn ) ->
                                    Infer.topLevelMember inferCtx declNode fn
                                        |> State.map (\member -> member :: acc)

                                Nothing ->
                                    State.pure acc
                        )
                        []
                    |> State.andThen
                        (\inferredMembers ->
                            inferredMembers
                                |> BindingGroup.solveGroup
                                    (Infer.unifyConfigForGroup inferCtx group)
                        )
            )



-- REGISTERING A MODULE'S DECLARATIONS


gatherTypeAliases : ModuleCtx -> File -> StateM (Dict GlobalKey TypeAlias)
gatherTypeAliases ctx file =
    let
        resolver : TypeResolver
        resolver =
            ctx.resolver

        moduleName : FullModuleName
        moduleName =
            ctx.thisIndex.moduleName

        moduleId : ModuleId
        moduleId =
            ctx.thisIndex.moduleId

        fileTypeAliases : Dict String Elm.Syntax.TypeAlias.TypeAlias
        fileTypeAliases =
            file.declarations
                |> List.foldl
                    (\node acc ->
                        case Node.value node of
                            Declaration.AliasDeclaration alias_ ->
                                Dict.insert (Node.value alias_.name) alias_ acc

                            _ ->
                                acc
                    )
                    Dict.empty
    in
    SCC.dictKeysStronglyConnectedComponents fileTypeAliases
        (\node ->
            case Dict.get node fileTypeAliases of
                Nothing ->
                    []

                Just alias_ ->
                    Elm.Syntax.TypeAnnotation.Extra.referencesToTypesFromModuleId
                        resolver
                        moduleId
                        (Node.value alias_.typeAnnotation)
        )
        |> State.concatAndFoldl
            (\node dict ->
                case Dict.get node fileTypeAliases of
                    Just typeAlias ->
                        let
                            toError : ErrorDetails -> Error
                            toError details =
                                { moduleName = FullModuleName.toModuleName moduleName
                                , declarationNames = [ Node.value typeAlias.name ]
                                , details = details
                                }
                        in
                        case
                            typeAlias.typeAnnotation
                                |> Node.value
                                |> TypeI.fromTypeAnnotation resolver dict
                        of
                            Err fromTypeAnnotationError ->
                                State.error (toError (TypeI.fromTypeAnnotationError fromTypeAnnotationError))

                            Ok type__ ->
                                let
                                    -- A record type alias also gets a constructor function
                                    -- (eg. `type alias Foo = { a : Int }` lets you write `Foo 1`).
                                    registerConstructor : MonoType -> StateM ()
                                    registerConstructor aliasMono =
                                        case Node.value typeAlias.typeAnnotation of
                                            TypeAnnotation.Record fields ->
                                                fields
                                                    |> Result.Extra.foldlWhileOk
                                                        (\(Node _ ( _, Node _ fieldType )) acc ->
                                                            case TypeI.fromTypeAnnotation resolver dict fieldType of
                                                                Err fromTypeAnnotationError ->
                                                                    Err (toError (TypeI.fromTypeAnnotationError fromTypeAnnotationError))

                                                                Ok fieldValueType ->
                                                                    Ok (fieldValueType :: acc)
                                                        )
                                                        []
                                                    |> State.fromResult
                                                    |> State.andThen
                                                        (\fieldTypesReverse ->
                                                            let
                                                                ctorType : MonoType
                                                                ctorType =
                                                                    fieldTypesReverse
                                                                        |> List.foldl (\fieldT acc -> Function { from = fieldT, to = acc }) aliasMono
                                                            in
                                                            State.addGlobalBinding
                                                                ( moduleId, "", Node.value typeAlias.name )
                                                                (TypeI.closeOver ctorType)
                                                        )

                                            _ ->
                                                State.pureUnit
                                in
                                State.do (registerConstructor type__) <| \() ->
                                State.pure <|
                                    Dict.insert
                                        ( moduleId, "", Node.value typeAlias.name )
                                        { args = List.map (\(Node.Node _ generic) -> TypeVar.parse generic) typeAlias.generics
                                        , type_ = type__
                                        }
                                        dict

                    Nothing ->
                        State.pure dict
            )
            (Dict.union ctx.inheritedAliases ctx.depTypeAliases)


registerConstructorsAndPorts : ModuleCtx -> Dict GlobalKey TypeAlias -> File -> StateM ()
registerConstructorsAndPorts ctx typeAliases file =
    file.declarations
        |> State.traverseUnit
            (\(Node _ declNode) ->
                case declNode of
                    Declaration.CustomTypeDeclaration customType ->
                        registerCustomType ctx.resolver typeAliases ctx.thisIndex.moduleId ctx.thisIndex.moduleName customType

                    Declaration.PortDeclaration sig ->
                        registerPort ctx.resolver typeAliases ctx.thisIndex.moduleId ctx.thisIndex.moduleName sig

                    _ ->
                        State.pureUnit
            )


registerCustomType :
    TypeResolver
    -> Dict GlobalKey TypeAlias
    -> ModuleId
    -> FullModuleName
    -> SyntaxType.Type
    -> StateM ()
registerCustomType resolver typeAliases moduleId moduleName customType =
    let
        typeName : String
        typeName =
            Node.value customType.name

        resultType : MonoType
        resultType =
            UserDefinedType
                { package = ""
                , moduleId = moduleId
                , name = typeName
                , args =
                    customType.generics
                        |> List.map
                            (\(Node _ g) ->
                                TypeVar
                                    (TypeVar.parse g)
                            )
                }
    in
    customType.constructors
        |> State.traverseUnit
            (\(Node _ { arguments, name }) ->
                let
                    argTypes : Result FromTypeAnnotationError (List MonoType)
                    argTypes =
                        arguments
                            |> Result.Extra.combineMap
                                (\(Node.Node _ arg) -> TypeI.fromTypeAnnotation resolver typeAliases arg)
                in
                case argTypes of
                    Err fromTypeAnnotationError ->
                        State.error
                            { moduleName = FullModuleName.toModuleName moduleName
                            , declarationNames = [ typeName ]
                            , details = TypeI.fromTypeAnnotationError fromTypeAnnotationError
                            }

                    Ok args ->
                        let
                            ctorType : MonoType
                            ctorType =
                                List.foldr (\argT acc -> Function { from = argT, to = acc }) resultType args
                        in
                        State.addGlobalBinding ( moduleId, "", Node.value name ) (TypeI.closeOver ctorType)
            )


registerPort :
    TypeResolver
    -> Dict GlobalKey TypeAlias
    -> ModuleId
    -> FullModuleName
    -> Signature
    -> StateM ()
registerPort resolver typeAliases moduleId moduleName sig =
    sig.typeAnnotation
        |> Node.value
        |> TypeI.fromTypeAnnotation resolver typeAliases
        |> Result.mapError
            (\fromTypeAnnotationError ->
                State.error
                    { moduleName = FullModuleName.toModuleName moduleName
                    , declarationNames = [ Node.value sig.name ]
                    , details = TypeI.fromTypeAnnotationError fromTypeAnnotationError
                    }
            )
        |> Result.map
            (\t ->
                State.addGlobalBinding
                    ( moduleId, "", Node.value sig.name )
                    (TypeI.closeOver t)
            )
        |> Result.Extra.merge


{-| Register the magic `command` / `subscription` values for `effect module`s.

The Elm compiler magically provides:

    command : MyCmd msg -> Cmd msg

    subscription : MySub msg -> Sub msg

`MyCmd` / `MySub` are the custom types named in the module header

    effect module Random where { command = MyCmd } exposing (..)

-}
registerEffectMagic : ModuleCtx -> StateM ()
registerEffectMagic ctx =
    if ctx.allowKernel then
        State.do (registerEffectCommand ctx) <| \() ->
        registerEffectSubscription ctx

    else
        State.pureUnit


registerEffectCommand : ModuleCtx -> StateM ()
registerEffectCommand ctx =
    case ctx.thisIndex.effectCommand of
        Nothing ->
            State.pureUnit

        Just myCmdName ->
            case ctx.resolver [] "Cmd" of
                Err _ ->
                    State.pureUnit

                Ok ( cmdPackage, cmdModuleId ) ->
                    let
                        msgVar : MonoType
                        msgVar =
                            TypeVar (TypeVar.parse "msg")

                        magicType : MonoType
                        magicType =
                            Function
                                { from =
                                    UserDefinedType
                                        { package = ""
                                        , moduleId = ctx.thisIndex.moduleId
                                        , name = myCmdName
                                        , args = [ msgVar ]
                                        }
                                , to =
                                    UserDefinedType
                                        { package = cmdPackage
                                        , moduleId = cmdModuleId
                                        , name = "Cmd"
                                        , args = [ msgVar ]
                                        }
                                }
                    in
                    State.addGlobalBinding
                        ( ctx.thisIndex.moduleId, "", ModuleIndex.effectCommandVar )
                        (TypeI.closeOver magicType)


registerEffectSubscription : ModuleCtx -> StateM ()
registerEffectSubscription ctx =
    case ctx.thisIndex.effectSubscription of
        Nothing ->
            State.pureUnit

        Just mySubName ->
            case ctx.resolver [] "Sub" of
                Err _ ->
                    State.pureUnit

                Ok ( subPackage, subModuleId ) ->
                    let
                        msgVar : MonoType
                        msgVar =
                            TypeVar (TypeVar.parse "msg")

                        magicType : MonoType
                        magicType =
                            Function
                                { from =
                                    UserDefinedType
                                        { package = ""
                                        , moduleId = ctx.thisIndex.moduleId
                                        , name = mySubName
                                        , args = [ msgVar ]
                                        }
                                , to =
                                    UserDefinedType
                                        { package = subPackage
                                        , moduleId = subModuleId
                                        , name = "Sub"
                                        , args = [ msgVar ]
                                        }
                                }
                    in
                    State.addGlobalBinding
                        ( ctx.thisIndex.moduleId, "", ModuleIndex.effectSubscriptionVar )
                        (TypeI.closeOver magicType)
