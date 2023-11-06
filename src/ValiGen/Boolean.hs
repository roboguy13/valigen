-- |

{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}

module ValiGen.Boolean
  -- (EventuallyTrue
  -- ,EventuallyFalse
  -- ,BoundedPred
  -- ,CoBoundedPred
  -- ,Alternating
  -- ,Unrestricted

  -- ,Boolean (..)

  -- ,getBoundaryET
  -- ,getBoundaryEF
  -- ,getRegion
  -- ,getCoRegion
  -- ,getNextTrue
  -- ,getNextFalse

  -- ,unrestricted
  -- ,lt, le, gt, ge, eq
  -- ,bounded
  -- ,cobounded
  -- )
  where

import Data.Functor.Contravariant
import Data.Coerce
import Control.Applicative

-- | exists n. forall x > n. p x
newtype EventuallyTrue a = EventuallyTrue a

-- | exists n. forall x > n. !(p x)
newtype EventuallyFalse a = EventuallyFalse a

-- | It's going to be False, then it will be True for a while and finally it will be False forever
-- For example: \x -> x > 2 && x < 10
-- It might also *always* be False (this is a sort of degenerate case).
--
-- exists m n. (forall m < x < n. p x) /\ (forall x <= m. !(p x)) /\ (forall x >= n. !(p x))
newtype BoundedPred a = BoundedPred (Maybe (a, a)) -- TODO: Should this be [] instead of Maybe?

-- | Contrast with `BoundedPred`. An example of `CoBoundedPred` is \x -> x <= 2 || x >= 10
newtype CoBoundedPred a = CoBoundedPred (Maybe (a, a)) -- NOTE: This has the region where it is *False*

-- | Example: \x -> x `mod` 5 == 0
-- At any point, there is always another True. Also, there is always another False.
--
-- (forall n. p n -> exists m > n. p m) /\ (forall n. !(p n) -> exists m > n. !(p m))
newtype Alternating a = Alternating (a -> Bool)
  deriving Contravariant via Predicate

newtype Unrestricted a = Unrestricted (a -> Bool)
  deriving Contravariant via Predicate

getBoundaryET :: EventuallyTrue a -> a
getBoundaryET (EventuallyTrue x) = x

getBoundaryEF :: EventuallyFalse a -> a
getBoundaryEF = getBoundaryET . notB

getRegion :: BoundedPred a -> Maybe (a, a)
getRegion (BoundedPred r) = r

getCoRegion :: CoBoundedPred a -> Maybe (a, a)
getCoRegion = getRegion . notB

getNextTrue :: Alternating a -> a -> a
getNextTrue = undefined

-- getNextFalse :: Alternating a -> a -> a
-- getNextFalse alt = getNextTrue (notB alt)

regionIntersect :: Ord a => Maybe (a, a) -> Maybe (a, a) -> Maybe (a, a)
regionIntersect _ Nothing = Nothing
regionIntersect Nothing _ = Nothing
regionIntersect (Just (px, py)) (Just (qx, qy))
  | py < qx = Nothing
  | otherwise = Just (max px qx, min py qy)

regionUnion :: Ord a => Maybe (a, a) -> Maybe (a, a) -> Maybe (a, a)
regionUnion p Nothing = p
regionUnion Nothing q = q
regionUnion (Just (px, py)) (Just (qx, qy))
  | qx > py = Nothing
  | otherwise = Just (min px qx, max py qy)

class Boolean f g | f -> g where
  (.&&) :: Ord a => f a -> f a -> f a
  (.||) :: Ord a => f a -> f a -> f a
  notB :: f a -> g a
  unrestrict :: Ord a => f a -> Unrestricted a

instance Boolean EventuallyTrue EventuallyFalse where
  EventuallyTrue x .&& EventuallyTrue y = EventuallyTrue (max x y)
  EventuallyTrue x .|| EventuallyTrue y = EventuallyTrue (min x y)
  notB (EventuallyTrue x) = EventuallyFalse x
  unrestrict (EventuallyTrue x) = Unrestricted (>= x)

instance Boolean EventuallyFalse EventuallyTrue where
  EventuallyFalse x .&& EventuallyFalse y = EventuallyFalse (min x y)
  EventuallyFalse x .|| EventuallyFalse y = EventuallyFalse (max x y)
  notB (EventuallyFalse x) = EventuallyTrue x
  unrestrict (EventuallyFalse x) = Unrestricted (< x)

instance Boolean BoundedPred CoBoundedPred where
  BoundedPred x .&& BoundedPred y = BoundedPred (regionIntersect x y)
  BoundedPred x .|| BoundedPred y = BoundedPred (regionUnion x y)
  notB (BoundedPred x) = CoBoundedPred x
  unrestrict (BoundedPred Nothing) = Unrestricted (const False)
  unrestrict (BoundedPred (Just (x, y))) = Unrestricted (\n -> n >= x && x < y)

instance Boolean CoBoundedPred BoundedPred where
  CoBoundedPred x .&& CoBoundedPred y = CoBoundedPred (regionUnion x y)
  CoBoundedPred x .|| CoBoundedPred y = CoBoundedPred (regionIntersect x y)
  notB (CoBoundedPred x) = BoundedPred x
  unrestrict (CoBoundedPred Nothing) = Unrestricted (const True)
  unrestrict (CoBoundedPred (Just (x, y))) = Unrestricted (\n -> n < x || n >= y)

-- instance Boolean Alternating Alternating where
--   Alternating f .&& Alternating g = Alternating (liftA2 (&&) f g)
--   Alternating f .|| Alternating g = Alternating (liftA2 (||) f g)
--   notB (Alternating f) = Alternating (not . f)
--   unrestrict = coerce

-- instance Boolean Unrestricted Unrestricted where
--   Unrestricted f .&& Unrestricted g = Unrestricted (liftA2 (&&) f g)
--   Unrestricted f .|| Unrestricted g = Unrestricted (liftA2 (||) f g)
--   notB (Unrestricted f) = Unrestricted (not . f)
--   unrestrict = id

-- unrestricted :: (a -> Bool) -> Unrestricted a
-- unrestricted = Unrestricted

-- lt :: Ord a => a -> EventuallyFalse a
-- lt x = EventuallyFalse (< x)

-- le :: Ord a => a -> EventuallyFalse a
-- le x = EventuallyFalse (<= x)

-- gt :: Ord a => a -> EventuallyTrue a
-- gt x = EventuallyTrue (> x)

-- ge :: Ord a => a -> EventuallyTrue a
-- ge x = EventuallyTrue (>= x)

-- eq :: Eq a => a -> BoundedPred a
-- eq x = BoundedPred (== x)

-- modAlt :: Integral a => a -> a -> Alternating a
-- modAlt m x = Alternating ((== x) . (`mod` m))

-- bounded :: EventuallyTrue a -> EventuallyFalse a -> BoundedPred a
-- bounded (EventuallyTrue f) (EventuallyFalse g) = BoundedPred (liftA2 (&&) f g)

-- coBounded :: EventuallyTrue a -> EventuallyFalse a -> CoBoundedPred a
-- coBounded (EventuallyTrue f) (EventuallyFalse g) = CoBoundedPred (liftA2 (||) f g)
