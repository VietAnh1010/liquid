{-# LANGUAGE NoMonomorphismRestriction #-}
{-@ LIQUID "--notermination"           @-}
{-@ LIQUID "--diff"                    @-}

module Demo.List where
  
import Prelude hiding (break)

-- data List a = Nil | Cons { head :: a, tail :: List a }

-- Haskell Type Definitions
plusOnes     :: [(Int, Int)]
mergeSort    :: (Ord a) => [a] -> [a]
quickSort    :: (Ord a) => [a] -> [a]
digits       :: Assoc String
sparseVec    :: Assoc Double
digsVec      :: Vec Int

-----------------------------------
-- Polymorphic Association Lists --
-----------------------------------

{-@ inline btwn @-}
btwn lo v hi = lo <= v && v <= hi

type AssocP k v = [(k, v)]
-- k and v are polymorphic, therefore k and v can be refined with predicates

{-@ digitsP :: AssocP {v:Int | btwn 0 v 9} String @-}
digitsP :: AssocP Int String
digitsP = [ (1, "one")
          , (2, "two")
          , (3, "three") ]

{-@ sparseVecP :: AssocP {v:Int | btwn 0 v 1000} Double @-}
sparseVecP :: AssocP Int Double
sparseVecP = [ (12 ,  34.1 )
             , (92 , 902.83)
             , (451,   2.95)
             , (877,   3.1 ) ]

-----------------------------------
-- Monomorphic Association Lists --
-----------------------------------

{-@ data Assoc v <p :: Int -> Bool> = KV { keyVals :: [(Int<p>, v)] } @-}
data Assoc v = KV [(Int, v)]
-- `newtype` does not work in liquid annotation, with abstract refinement
-- `type` does not work either

{-@ digits :: Assoc (String) <{\v -> btwn 0 v 9}> @-}
digits    = KV [ (1, "one")
               , (2, "two")
               , (3, "three") ]


{-@ sparseVec :: Assoc Double <{\v -> btwn 0 v 1000}> @-}
sparseVec = KV [ (12 ,  34.1 )
               , (92 , 902.83)
               , (451,   2.95)
               , (877,   3.1 ) ]

----------------------
-- Dependent Tuples --
----------------------

-- `break` from the Prelude.
{-@ break :: (a -> Bool) -> x:[a] -> ([a], [a])<\y -> {z:[a] | len x = len y + len z}> @-}
break                   :: (a -> Bool) -> [a] -> ([a], [a])
break _ []              =  ([], [])
break p xs@(x:xs')
  | p x        = ([], xs)
  | otherwise  = let (ys, zs) = break p xs' in (x:ys, zs)

-- Dependent Tuples via Abstract Refinements
-- data (a, b)<p :: a -> b -> Prop> = (x:a, b<p x>)
-- Instantiate the `p` in *different* ways.

{-@ plusOnes :: [(Int, Int)<{\x1 x2 -> x2 = x1 + 1}>] @-}
plusOnes = [(0, 1), (5, 6), (999, 1000)]

------------------------------
-- Abstractly Refined Lists --
------------------------------

-- data [a] <p :: a -> a -> Prop> 
--   = []  
--   | (:) (hd :: a) (tl :: [a<p h>]<p>) -> [a]<p>

-- * The type is parameterized with a refinement `p :: a -> a -> Prop`
--   Think of `p` as a *binary relation* over the `a` values comprising
--   the list.

-- * The empty list `[]` is a `[a]<p>`. Clearly, the empty list has no
--   elements whatsoever and so every pair is trivially, or rather,
--   vacuously related by `p`.

-- * The cons constructor `(:)` takes a head `hd` of type `a` and a tail
--   `tl` of `a<p h>` values, each of which is *related to* `h` **and** which
--   (recursively) are pairwise related `[...]<p>` and returns a list where
--   *all* elements are pairwise related `[a]<p>`.

------------------------------------
-- Using Abstractly Refined Lists --
------------------------------------

-- For starters, we can define a few helpful type aliases.

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type DecrList a = [a]<{\xi xj -> xi >= xj}> @-}
{-@ type UniqList a = [a]<{\xi xj -> xi /= xj}> @-}


{-@ whatGosUp :: IncrList Integer @-}
whatGosUp :: [Integer]
whatGosUp = [1,2,3]

{-@ mustGoDown :: DecrList Integer @-}
mustGoDown :: [Integer]
mustGoDown = [3,2,1]

{-@ noDuplicates :: UniqList Integer @-}
noDuplicates :: [Integer]
noDuplicates = [1,3,2]

--------------------
-- Insertion Sort --
--------------------

{-@ insertSort :: Ord a => [a] -> IncrList a @-}
insertSort :: Ord a => [a] -> [a]
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

-- without this annotation, LH reports the following error:
-- Liquid Type Mismatch
--     .
--     The inferred type
--       VV : a
--     .
--     is not a subtype of the required type
--       VV : {VV : a | ?a <= VV}
--     .
--     in the context
--       ?a : a
--     Constraint id 1
--
{-@ insert :: Ord a => a -> IncrList a -> IncrList a @-}
insert :: Ord a => a -> [a] -> [a]
insert y []     = [y]
insert y (x:xs)
  | y <= x      = y : x : xs
  | otherwise   = x : insert y xs

-- If you prefer the more Haskelly way of writing insertion sort,
-- i.e. with a `foldr`, that works too. Can you figure out why?
{-@ insertSort' :: Ord a => [a] -> IncrList a @-}
insertSort' :: Ord a => [a] -> [a]
insertSort' = foldr insert []

----------------
-- Merge Sort --
----------------

split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
  where
    (xs, ys)   = split zs
split xs       = (xs, [])


-- {-@ merge :: (Ord a) => IncrList a -> IncrList a -> IncrList a @-}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

{-@ mergeSort :: (Ord a) => [a] -> IncrList a @-}
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs)  = split xs

----------------
-- Quick Sort --
----------------

{-@ quickSort    :: (Ord a) => [a] -> IncrList a @-}
quickSort []     = []
quickSort (x:xs) = pivApp x lts gts
  where
    fs           = [y | y <- xs, y < x ]
    ss           = [z | z <- xs, z >= x]
    -- even with this annotation, LH still cannot infer the corect type for pivApp
    -- {-@ lts :: IncrList {v:a | v < x} @-}
    -- {-@ gts :: IncrList {v:a | v >= x} @-}
    lts          = quickSort fs
    gts          = quickSort ss
    
{-@ pivApp :: piv:a -> IncrList {v:a | v <  piv} -> IncrList {v:a | v >= piv} -> IncrList a @-}
pivApp piv []     ys  = piv : ys
pivApp piv (x:xs) ys  = x   : pivApp piv xs ys

-- Really Sorting Lists
-- --------------------

-- The convenient thing about our encoding is that the
-- underlying datatype is plain Haskell lists.
-- By decoupling (or rather, parameterizing)
-- the relation or property or invariant from the actual
-- data structure we can plug in different invariants,
-- sometimes in the *same* program.

-- To see why this is useful, lets look at a *real-world*
-- sorting algorithm: the one used inside GHC's
-- `Data.List` [module][ghc-list].

{-@ sort :: (Ord a) => [a] -> IncrList a  @-}
sort = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs
    sequences [x] = [[x]]
    sequences []  = [[]]

    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs

    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs       = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []


---------------------------------------------------------------
-- User-defined Lists
---------------------------------------------------------------

-- The earlier definition is baked into LiquidHaskell's prelude,
-- since its for GHC Lists.
-- For completeness, lets illustrate the method on a new list type.

data Vec a = Null | Cons a (Vec a)

{-@ data Vec a <p :: a -> a -> Bool> 
      = Null
      | Cons (h :: a) (t :: Vec <p> (a<p h>))
  @-}

{-@ type IncrVec a = Vec <{\xi xj -> xi <= xj}> a @-}

{-@ digsVec :: IncrVec Int @-}
digsVec     = Cons 0 (Cons 1 (Cons 2 Null))
