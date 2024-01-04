{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--diff"                      @-}
{-@ LIQUID "--counter-examples"          @-}

module Demo.F91 where

import Language.Haskell.Liquid.ProofCombinators

{-@ lazy f91 @-}
f91 :: Int -> Int
f91 n = if n > 100 then n - 10 else f91 (f91 (n + 11))

{-@ f91 :: n:Int -> {v:Int | if n > 100 then v = n - 10 else v = 91} @-}
-- LH cannot infer this property, but it can verify this property.
-- comment this out and the program will be marked unsafe!

-- {-@ reflect f91 @-}
-- {-@ f91_gt_100 :: n:{v: Int | v > 100} -> {f91 n == n - 10} @-}
-- f91_gt_100 :: Int -> Proof
-- f91_gt_100 _ = ()

-- {-@ f91_btw_90_100 :: n:{v:Int | 90 <= n && n <= 100} -> {f91 n = f91 (n + 1)} @-}
-- f91_btw_90_100 :: Int -> Proof
-- f91_btw_90_100 n = 
--         f91 n
--     ==. f91 (f91 (n + 11))
--     ==. f91 (n + 1) ? f91_gt_100
--     *** QED

-- {-@ f91_le_100 :: n:{v:Int | v <= 100} -> {f91 n == 91} / [100 - n] @-}
-- f91_le_100 :: Int -> Proof
-- f91_le_100 n
--   | n == 100 =
--         f91 n
--     ==. f91 (n + 1) ? f91_btw_90_100
--     ==. 91 ? f91_gt_100
--     *** QED
--   | 90 <= n && n < 100 =
--         f91 n
--     ==. 91 ? f91_le_100 (n + 1)
--     *** QED
--   | otherwise =
--         f91 n
--     ==. f91 (f91 (n + 11))
--     ==. f91 91 ? f91_le_100 (n + 11)
--     ==. 91 ? f91_le_100 91
--     *** QED

foo :: Int -> Int
foo n
  | n > 100 = n
  | otherwise = if f91 n == 91 then 91 else error "f91 does not return 91?"
-- the error branch is dead code. The program should be safe
