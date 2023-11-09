-- |

module ValiGen.Int where

import ValiGen.Boolean

import Test.QuickCheck
import Control.Applicative

type Basic = (Int, Int)
type Open = [Basic]

contains :: Basic -> Basic -> Bool
(x1, y1) `contains` (x2, y2) =
  x1 <= x2 && y1 >= y2

inBasic :: Int -> Basic -> Bool
n `inBasic` (x, y) = n >= x && n <= y

intersects :: Basic -> Basic -> Bool
(x1, y1) `intersects` b@(x2, y2) =
  x1 `inBasic` b || y1 `inBasic` b

genInt :: ToOpen a => a -> Gen Int
genInt = oneof . map choose . toOpen

type ProductTerm a = (BooleanTerm a, a -> BooleanTerm a)

genPair :: ProductTerm Int -> Gen (Int, Int)
genPair (x, f) = do
  a <- genInt x
  b <- genInt (f a)
  pure (a, b)

ge :: Int -> BooleanTerm Int
ge = TEventuallyTrue . EventuallyTrue

gt :: Int -> BooleanTerm Int
gt = TEventuallyTrue . EventuallyTrue . succ

le :: Int -> BooleanTerm Int
le = TEventuallyFalse . EventuallyFalse

lt :: Int -> BooleanTerm Int
lt = TEventuallyFalse . EventuallyFalse . pred

class ToOpen a where
  toOpen :: a -> Open

instance ToOpen (EventuallyTrue Int) where
  toOpen (EventuallyTrue x) = [(x, maxBound)]

instance ToOpen (EventuallyFalse Int) where
  toOpen (EventuallyFalse x) = [(minBound, x)]

instance ToOpen (BoundedPred Int) where
  toOpen (BoundedPred Nothing) = []
  toOpen (BoundedPred (Just (x, y))) = [(x, y)]

instance ToOpen (CoBoundedPred Int) where
  toOpen (CoBoundedPred Nothing) = [(minBound, maxBound)]
  toOpen (CoBoundedPred (Just (x, y))) = [(minBound, x-1), (y+1, maxBound)]

instance ToOpen (BooleanTerm Int) where
  toOpen (TEventuallyTrue x) = toOpen x
  toOpen (TEventuallyFalse x) = toOpen x
  toOpen (TAnd x y) = openIntersect (toOpen x) (toOpen y)
  toOpen (TOr x y) = openUnion (toOpen x) (toOpen y)
  toOpen (TNot x) = undefined -- TODO: Implement
  toOpen (TBounded x) = toOpen x
  toOpen (TCoBounded x) = toOpen x

openUnion :: Open -> Open -> Open
openUnion = foldr insertBasic

openIntersect :: Open -> Open -> Open
openIntersect = foldr intersectBasicOpen

intersectBasicOpen :: Basic -> Open -> Open
intersectBasicOpen _ [] = []
intersectBasicOpen b (x:xs) =
  case basicIntersect b x of
    Nothing -> x : intersectBasicOpen b xs
    Just b' -> b' : xs

insertBasic :: Basic -> Open -> Open
insertBasic b [] = [b]
insertBasic b (x:xs) =
  case mergeIntoBasic b x of
    Nothing -> x : insertBasic b xs
    Just b' -> insertBasic b' xs

basicIntersect :: Basic -> Basic -> Maybe Basic
basicIntersect (px, py) (qx, qy)
  | py < qx = Nothing
  | otherwise = Just (max px qx, min py qy)

basicUnion :: Basic -> Basic -> Maybe Basic
basicUnion (px, py) (qx, qy)
  | qx > py = Nothing
  | otherwise = Just (min px qx, max py qy)

mergeIntoBasic :: Basic -> Basic -> Maybe Basic
mergeIntoBasic a b
  | b `contains` a = Just b
  | a `contains` b = Just a
  | otherwise = Nothing
  -- | otherwise = basicIntersect a b

-- class GenInt a where
--   genInt :: a -> Gen Int

-- instance GenInt Basic where
--   genInt = choose

-- instance GenInt Open where
--   genInt = oneof . map genInt

-- instance GenInt (EventuallyTrue Int) where
--   genInt (EventuallyTrue x) = choose (x, maxBound)

-- instance GenInt (EventuallyFalse Int) where
--   genInt (EventuallyFalse x) = choose (minBound, x)

-- instance GenInt (BoundedPred Int) where
--   genInt (BoundedPred Nothing) = discard
--   genInt (BoundedPred (Just p)) = choose p

-- instance GenInt (CoBoundedPred Int) where
--   genInt (CoBoundedPred Nothing) = arbitrary
--   genInt (CoBoundedPred (Just (x, y))) =
--     oneof [choose (minBound, x-1)
--           ,choose (y+1, maxBound)
--           ]

-- instance GenInt (BooleanTerm Int) where
--   genInt (TEventuallyTrue p) = genInt p
--   genInt (TEventuallyFalse p) = genInt p
--   genInt (TBounded p) = genInt p
--   genInt (TCoBounded p) = genInt p
--   genInt (TAnd p q) = genInt (TOr (notB p) (notB q)) -- TODO: Does this work well enough?
--   genInt (TOr p q) = oneof [genInt p, genInt q]
--   genInt (TNot p) = genInt (notB p)

-- -- | For example:
-- --     require (`mod` 2) (lt 1)
-- --   becomes
-- --     map (*2) (genInt anything)
-- --
-- --   and
-- --     genInt (require (coPrime ))
-- require :: (Int -> Int) -> BooleanTerm Int -> Gen Int
-- require = undefined
