module List.ExtraExtra exposing (findLastMap, zipOrNothingIfLengthsDiffer)

{-| -}


{-| Like `List.Extra.findMap` but checking from the end
-}
findLastMap : (a -> Maybe b) -> List a -> Maybe b
findLastMap toMaybeFound list =
    list
        |> List.foldr
            (\el maybeAlreadyFound ->
                case maybeAlreadyFound of
                    Just _ ->
                        maybeAlreadyFound

                    Nothing ->
                        toMaybeFound el
            )
            Nothing


zipOrNothingIfLengthsDiffer : List a -> List b -> Maybe (List ( a, b ))
zipOrNothingIfLengthsDiffer args1 args2 =
    case args1 of
        [] ->
            case args2 of
                [] ->
                    justListEmpty

                _ :: _ ->
                    Nothing

        a1 :: rest1 ->
            case args2 of
                a2 :: rest2 ->
                    case zipOrNothingIfLengthsDiffer rest1 rest2 of
                        Just lst ->
                            Just (( a1, a2 ) :: lst)

                        Nothing ->
                            Nothing

                [] ->
                    Nothing


justListEmpty : Maybe (List a)
justListEmpty =
    Just []
