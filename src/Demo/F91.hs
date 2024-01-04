module Demo.F91 where

{-@ LIQUID "--counter-example" @-}

{-@ f91 :: n:Int -> {v:Int | if n > 100 then v = n - 10 else v = 91} @-}
f91 :: Int -> Int
f91 n 
  | n > 100 = n - 10
  | otherwise = f91 (f91 (n + 11))
-- fail to infer, even with annotation

foo :: Int -> Int
foo n
  | n > 100 = n --f91 n = n - 10 for n > 100
  | otherwise = if f91 n == 91 then 91 else error "f91 does not return 91?"

-- we expect that liquid haskell can infer that f91 always return 91 for n <= 100
-- and therefore the error branch is dead code
-- without any annotation, does not work. But I can't understand the error message

