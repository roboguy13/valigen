-- |

module ValiGen.Int where

import ValiGen.Boolean

import Test.QuickCheck
import Control.Applicative

class GenInt a where
  genInt :: a -> Gen Int

instance GenInt (EventuallyTrue Int) where
  genInt (EventuallyTrue x) = choose (x, maxBound)

instance GenInt (EventuallyFalse Int) where
  genInt (EventuallyFalse x) = choose (minBound, x)

instance GenInt (BoundedPred Int) where
  genInt (BoundedPred Nothing) = discard
  genInt (BoundedPred (Just p)) = choose p

instance GenInt (CoBoundedPred Int) where
  genInt (CoBoundedPred Nothing) = arbitrary
  genInt (CoBoundedPred (Just (x, y))) =
    oneof [choose (minBound, x-1)
          ,choose (y+1, maxBound)
          ]

instance GenInt (BooleanTerm Int) where
  genInt (TEventuallyTrue p) = genInt p
  genInt (TEventuallyFalse p) = genInt p
  genInt (TBounded p) = genInt p
  genInt (TCoBounded p) = genInt p
  genInt (TAnd p q) = genInt (TOr (notB p) (notB q)) -- TODO: Does this work well enough?
  genInt (TOr p q) = oneof [genInt p, genInt q]
  genInt (TNot p) = genInt (notB p)