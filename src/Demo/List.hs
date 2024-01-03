module Demo.List where

data List a = Nil | Cons { head :: a, tail :: List a }

{-
{-@ mkList :: Int -> k:Int -> List {v:Int | k < v} @-} is rejected
Liquid Type Mismatch
    .
    The inferred type
      VV : GHC.Types.Int
    .
    is not a subtype of the required type
      VV : {VV##932 : GHC.Types.Int | k##a10dl < VV##932}
    .
    in the context
      k##a10dl : GHC.Types.Int
    Constraint id 11
-}

{-@ mkList :: Int -> k:Int -> List {v:Int | k <= v} @-}
mkList :: Int -> Int -> List Int
mkList n k =
  if 0 < n
    then Cons k $ mkList (n - 1) (k + 1)
    else Nil
