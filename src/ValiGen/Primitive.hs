-- |

module ValiGen.Primitive where

import ValiGen.Refine

import Test.QuickCheck

data Primitive a = Lt (TwoPoint a) | Le (TwoPoint a) | Gt (TwoPoint a) | Ge (TwoPoint a) | DivisibleBy a
  deriving (Show)

primitiveValidate :: Primitive Int -> Int -> Bool
primitiveValidate (Lt x) y = TwoPoint y < x
primitiveValidate (Le x) y = TwoPoint y <= x
primitiveValidate (Gt x) y = TwoPoint y > x
primitiveValidate (Ge x) y = TwoPoint y >= x
primitiveValidate (DivisibleBy x) y = y `mod` x == 0

primitiveRefine :: Primitive Int -> RefinedInt
primitiveRefine (Lt x) = refinedFromDomain (Range (minBound, x-1))
primitiveRefine (Le x) = refinedFromDomain (Range (minBound, x))
primitiveRefine (Gt x) = refinedFromDomain (Range (x+1, maxBound))
primitiveRefine (Ge x) = refinedFromDomain (Range (x, maxBound))
primitiveRefine (DivisibleBy x) = refinedFromMap (*x) invMul
  where
    invMul 1 = 1
    invMul a = a `div` x

data Boolean a = Prim a | And (Boolean a) (Boolean a) | Or (Boolean a) (Boolean a)
  deriving (Show)

type Boolean' a = Boolean (Primitive a)

booleanRefine :: Boolean' Int -> [RefinedInt]
booleanRefine (Prim p) = [primitiveRefine p]
booleanRefine (And x y) = do
  -- We distribute the @And@ over the @Or@s
  a <- booleanRefine x
  b <- booleanRefine y
  pure (a <> b) -- Here, (<>) is a kind of conjunction
booleanRefine (Or x y) = booleanRefine x ++ booleanRefine y

fromRefine :: [RefinedInt] -> Gen Int
fromRefine = oneof . map refineGen

refined :: Boolean' Int -> Gen Int
refined = fromRefine . booleanRefine

lt, le, gt :: TwoPoint a -> Boolean' a
lt = Prim . Lt
le = Prim . Le
gt = Prim . Gt
ge = Prim . Ge
divisibleBy = Prim . DivisibleBy

(/\), (\/) :: Boolean a -> Boolean a -> Boolean a
(/\) = And
(\/) = Or
