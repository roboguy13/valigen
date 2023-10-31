{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module ValiGen.ValiGen
  where

import Test.QuickCheck
import Data.List
import Data.Profunctor
import Data.Bifunctor
import Control.Monad

data ValiGen' v a b
  = Var v
  | OneOf [b]
  | Choose (b, b)
  | Not (ValiGen' v a b)
  | Union (ValiGen' v a b) (ValiGen' v a b)
  | Intersect (ValiGen' v a b) (ValiGen' v a b)
  | forall c. Implies (ValiGen' v a c) (v -> ValiGen' v a b)
  | Basic (BasicFn a b)
  | Check (a -> Bool)

type ValiGen v a = ValiGen' v a a

data BasicFn a b = BasicFn (a -> Bool) (Gen b)

instance Profunctor BasicFn where
  dimap f g (BasicFn p q) = BasicFn (p . f) (fmap g q)

instance Profunctor (ValiGen' v) where
  dimap _ _ (Var v) = Var v
  dimap _ g (OneOf xs) = OneOf $ map g xs
  dimap _ g (Choose p) = Choose $ bimap g g p
  dimap f g (Not x) = Not $ dimap f g x
  dimap f g (Union x y) = Union (dimap f g x) (dimap f g y)
  dimap f g (Intersect x y) = Intersect (dimap f g x) (dimap f g y)
  dimap f g (Implies x h) = Implies (dimap f g x) (dimap f g . h)
  dimap f g (Basic b) = Basic $ dimap f g b
  dimap f _ (Check h) = Check $ h . f

instance Functor (ValiGen' v a) where fmap = dimap id

instance Applicative (ValiGen' v a) where
  pure x = OneOf [x]
  (<*>) = ap

instance Monad (ValiGen' v a) where
  return = pure
  Var x >>= _ = Var x
  OneOf xs >>= f = join $ OneOf $ map f xs -- TODO: Does this work?
  Not x >>= f = Not (x >>= f)
  Union x y >>= f = Union (x >>= f) (y >>= f)
  Intersect x y >>= f = Intersect (x >>= f) (y >>= f)
  Implies x k >>= f = Implies x (k >=> f)

-- mkBasic :: (a -> Bool) -> Gen a -> ValiGen v a
-- mkBasic x = Basic . BasicFn x

-- class Negate a where
--   neg :: a -> a

-- data ChooseUnion a
--   = Range (a, a)
--   | ChooseUnion (ChooseUnion a) (ChooseUnion a)

-- instance Semigroup (ChooseUnion a) where
--   (<>) = ChooseUnion

-- -- | NbE-style interpretation
-- data Value a
--   = VNeutral (Neutral a)
--   | VOneOf [a]
--   | VChooseUnion (ChooseUnion a)
--   | VOneOfChoose [a] (ChooseUnion a)
--   -- | VTrue

-- data Neutral a
--   = NNot (Value a)
--   | NImplies (Neutral a) (Abstraction a)
--   | NUnion1 (Neutral a) (Value a)
--   | NUnion2 (Value a) (Neutral a)
--   | NIntersect1 (Neutral a) (Value a)
--   | NIntersect2 (Value a) (Neutral a)

-- newtype Abstraction a = Abstraction { runAbstraction :: Value a -> Value a }

-- validate :: Eq a => Value a -> (a -> Bool)
-- validate (VNeutral n) z = validateNeutral n z
-- validate (VOneOf xs) z = z `elem` xs

-- validateNeutral :: Eq a => Neutral a -> (a -> Bool)
-- validateNeutral (NNot x) z = not $ validate x z
-- validateNeutral (NImplies x f) z = validateNeutral x z || not (validate (runAbstraction f (VNeutral x)) z)
-- validateNeutral (NUnion1 x y) z = validateNeutral x z || validate y z
-- validateNeutral (NUnion2 x y) z = validate x z || validateNeutral y z
-- validateNeutral (NIntersect1 x y) z = validateNeutral x z && validate y z
-- validateNeutral (NIntersect2 x y) z = validate x z && validateNeutral y z

-- gen :: Enum a => Value a -> Gen a
-- gen (VOneOf xs) = elements xs
-- gen (VChooseUnion p) = genChooseUnion p
-- gen (VOneOfChoose xs p) = oneof [genChooseUnion p, elements xs]
-- gen (VNeutral n) = genNeutral n

-- genChooseUnion :: Enum a => ChooseUnion a -> Gen a
-- genChooseUnion (Range p) = chooseEnum p
-- genChooseUnion (ChooseUnion x y) = oneof [genChooseUnion x, genChooseUnion y]

-- genNeutral :: Enum a => Neutral a -> Gen a
-- genNeutral (NNot x) = error "genNeutral NNot"
-- genNeutral (NImplies x f) = genNeutral x >>= (gen . runAbstraction f . VOneOf . (:[]))
-- genNeutral (NIntersect1 x y) = oneof [genNeutral x, gen y]
-- genNeutral (NIntersect2 x y) = oneof [gen x, genNeutral y]
-- genNeutral (NUnion1 {}) = error "genNeutral NUnion1"
-- genNeutral (NUnion2 {}) = error "genNeutral NUnion2"

-- reify :: Value a -> ValiGen v a
-- reify = undefined

-- eval :: Eq a => ValiGen (Value a) a -> Value a
-- eval vg = case vg of
--   Var x -> x
--   OneOf xs -> VOneOf xs
--   Implies x f -> --VNeutral $ NImplies (eval x) $ Abstraction (eval . f)
--     case eval x of
--       VNeutral nX -> VNeutral $ NImplies nX $ Abstraction (eval . f)
--       xV -> eval $ f xV
--   Union x y -> evalUnion x y
--   Not x -> evalNot x

-- evalNot :: Eq a => ValiGen (Value a) a -> Value a
-- evalNot = \case
--   Intersect x y -> evalUnion (Not x) (Not y)
--   _ -> error "evalNot: something other than Intersect"

-- evalUnion :: Eq a => ValiGen (Value a) a -> ValiGen (Value a) a -> Value a
-- evalUnion x y =
--   case eval x of
--     VNeutral nX -> VNeutral $ NUnion1 nX $ eval y
--     VOneOf xs -> evalUnion2 (VOneOf xs) y
--     VChooseUnion p -> evalUnion2 (VChooseUnion p) y

-- evalUnion2 :: Eq a => Value a -> ValiGen (Value a) a -> Value a
-- evalUnion2 xV y =
--   case eval y of
--     VNeutral nY -> VNeutral $ NUnion2 xV nY
--     yV -> liftedUnion xV yV

-- liftedUnion :: Value a -> Value a -> Value a
-- liftedUnion (VOneOf xs) y = unionOneOf xs y
-- liftedUnion (VChooseUnion p) y = unionChoose p y
-- liftedUnion x (VOneOf ys) = unionOneOf ys x
-- liftedUnion x (VChooseUnion p) = unionChoose p x
-- liftedUnion (VOneOfChoose xs p) y = unionChoose p (unionOneOf xs y)
-- liftedUnion x (VOneOfChoose ys p) = unionChoose p (unionOneOf ys x)

-- liftedIntersect :: Eq a => Value a -> Value a -> Value a
-- liftedIntersect (VOneOf xs) y = intersectOneOf xs y
-- liftedIntersect (VChooseUnion p) y = intersectChoose p y

-- unionOneOf :: [a] -> Value a -> Value a
-- unionOneOf xs (VOneOf ys) = VOneOf (xs ++ ys)
-- unionOneOf xs (VOneOfChoose ys p) = VOneOfChoose (xs ++ ys) p
-- unionOneOf xs (VChooseUnion p) = VOneOfChoose xs p

-- unionChoose :: ChooseUnion a -> Value a -> Value a
-- unionChoose p (VChooseUnion q) = VChooseUnion (p <> q)
-- unionChoose p (VOneOf ys) = unionOneOf ys (VChooseUnion p)
-- unionChoose p (VOneOfChoose ys q) = VOneOfChoose ys (p <> q)

-- intersectOneOf :: Eq a => [a] -> Value a -> Value a
-- intersectOneOf xs (VOneOf ys) = VOneOf (nub xs `intersect` nub ys) -- TODO: Use Sets
-- intersectOneOf xs (VChooseUnion p) = undefined -- TODO: Implement

-- intersectChoose :: Eq a => ChooseUnion a -> Value a -> Value a
-- intersectChoose = undefined
