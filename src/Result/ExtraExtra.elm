module Result.ExtraExtra exposing (concatAndFoldl)

import Result.Extra


concatAndFoldl : (a -> value -> Result error value) -> value -> List (List a) -> Result error value
concatAndFoldl reduce initialAcc listOfLists =
    Result.Extra.foldlWhileOk
        (\innerList acc -> Result.Extra.foldlWhileOk reduce acc innerList)
        initialAcc
        listOfLists
