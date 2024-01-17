{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality"    @-}

module Demo.ItvSet where
    
data ItvSet a 
    = Empty
    | I { from :: a
        , to   :: a
        , rest :: ItvSet a
        }

-- why do we need to use a polymorphic `a` here?
-- because we need this polymorphic `a` to refine `from`, `to` and `rest` with different
-- predicates

{-@
data ItvSet a
    = Empty
    | I { from :: a
        , to   :: {v:a | from < v}
        , rest :: ItvSet {v:a | to <= v}
        }
@-}

{-@ type Nat = {v:Int | v >= 0} @-}

-- there is no empty interval. The left bound of the interval must be less than
-- the right bound of the interval (from < to)
-- also, all intervals in `rest` must have left and right bounds that are greater than
-- the right bound of the current interval (to the right of the current interval)
-- |--- current interval ---| |--- remaining intervals ---|
i0 = I 0 1 Empty -- ok

-- i1 = I 1 0 Empty -- rejected
-- type of `0` is infered as {v:Int | v == 0} = T0
-- based on the annotation provided above, this type must be a subtype of {v:Int | 1 < v} = T1
-- SMT solver checks `v == 0 => 1 < v`: FALSE
-- The statement is false, hence T0 not subtype T1, hence reject

-- i2 = I 1 7 (I 5 8 Empty) -- rejected
-- Liquid Type Mismatch
--     
--     The inferred type
--       VV : GHC.Num.Integer.Integer
--     
--     is not a subtype of the required type
--       VV : {VV##853 : GHC.Num.Integer.Integer | (7 : int) <= VV##853}
-- {v:Int | v == 5} is not subtype of {v:Int | 7 <= v}
-- SMT solver checks `v == 5 => 7 <= v`: FALSE


{-@ union :: ItvSet Nat -> ItvSet Nat -> ItvSet Nat @-}
union :: ItvSet Int -> ItvSet Int -> ItvSet Int
-- needed, otherwise error:
-- Specified type does not refine Haskell type for `Demo.IntervalSet.union` (Plugged Init types old)
-- The Liquid type
-- 
--     (Demo.IntervalSet.ItvSet GHC.Types.Int) -> (Demo.IntervalSet.ItvSet GHC.Types.Int) -> (Demo.IntervalSet.ItvSet GHC.Types.Int)
-- 
-- is inconsistent with the Haskell type
-- 
--     forall t ->
-- (GHC.Classes.Ord t, GHC.Num.Num t) =>
-- Demo.IntervalSet.ItvSet t
-- -> Demo.IntervalSet.ItvSet t -> Demo.IntervalSet.ItvSet t
-- 
-- defined at /home/vanh1010/liquid/src/Demo/IntervalSet.hs:48:1-5
-- 
-- Specifically, the Liquid component
-- 
--     {VV##0 : GHC.Types.Int | VV##0 >= 0}
-- 
-- is inconsistent with the Haskell component
-- 
--     t
--
union is1 is2 = go 0 is1 is2
  where
    go _ is Empty = is
    go _ Empty is = is
    go lb is1@(I f1 t1 ris1) is2@(I f2 t2 ris2)
      | t1 < t2 = go lb is2 is1

      -- t1 >= t2      
      -- f1 > t2, disjoint: |f2 t2| |f1 t1| ... (t1 > f1 > t2 > f2)
      | f1 > t2 = I f2 t2 (go t2 (I f1 t1 ris1) ris2)
      -- | f1 > t2 = I f2 t2 (go t2 (I f1 t2 is1) is2) -- rejected. Problem: f1 < t1 (inv)
      -- | f1 > t2 = I f2 t2 (go t2 is1 ris2) -- rejected, despite `is1 = I f1 t1 ris1`
      -- `lb` is needed, so that LH can infer that
      -- `go t2 ...` :: ItvSet {v:Int | v >= t2}`
      -- without `lb`, LH reports error. Although `lb` is useless

      -- f1 <= t2, overlapping: |f1/f2 |f1/f2 t2| t1| ...
      | otherwise = go f' (I f' t1 ris1) ris2
      where 
        f' = min f1 f2
