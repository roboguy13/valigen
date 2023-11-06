-- |

module ValiGen.Range where

import ValiGen.Boolean

data Range = Range Int Int

  -- | A union of ranges
type Open = [Range]

class FilterRange a where
  filterRange :: a -> Range -> Range

instance FilterRange (EventuallyTrue Int) where
