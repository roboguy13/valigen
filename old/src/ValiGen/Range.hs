-- |

module ValiGen.Range where

import ValiGen.Boolean

-- | Invariant: Given
--     Range (Just (x, y))
--   we require that x <= y
newtype Range = Range (Int, Int)

  -- | A union of ranges
type Open = [Range]

class FilterRange a where
  filterRange :: a -> Range -> Open
  -- filterOpen :: a -> Open -> Open

filterOpen :: FilterRange a => a -> Open -> Open
filterOpen x = concatMap (filterRange x)

unionR :: Range -> Range -> Open
unionR = undefined

intersectR :: Range -> Range -> Range
intersectR = undefined

unionO :: Open -> Open -> Open
unionO = undefined

intersectO :: Open -> Open -> Open
intersectO = undefined

instance FilterRange (EventuallyTrue Int) where
  filterRange (EventuallyTrue n) (Range (x, y))
    | y < n = []
    | otherwise = [Range (x `max` n, y)]

instance FilterRange (EventuallyFalse Int) where
  filterRange (EventuallyFalse n) (Range (x, y))
    | x >= n = []
    | otherwise = [Range (x, y `min` n)]

instance FilterRange (BoundedPred Int) where
  filterRange (BoundedPred Nothing) _ = []
  filterRange (BoundedPred (Just (bX, bY))) (Range (x, y))
    | y < bY || x >= bX = []
    | otherwise =
        [Range (x `max` bX, y `min` bY)]

-- TODO: Does this make sense?
instance FilterRange (CoBoundedPred Int) where
  filterRange (CoBoundedPred Nothing) _ = []
  filterRange (CoBoundedPred (Just (bX, bY))) (Range (x, y))
    | y >= bY || x < bX = []
    | otherwise =
        [Range (x `min` bX, y `max` bY)]

filterWithTerm :: BooleanTerm Int -> Range -> Open
filterWithTerm t r =
  case t of
    TEventuallyTrue p -> filterRange p r
    TEventuallyFalse p -> filterRange p r
    TBounded p -> filterRange p r
    TCoBounded p -> filterRange p r
    TAnd p q -> intersectO (filterWithTerm p r) (filterWithTerm q r)
    TOr p q -> unionO (filterWithTerm p r) (filterWithTerm q r)
