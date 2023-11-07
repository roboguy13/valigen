-- |

module Examples.Int where

import ValiGen.Int
import ValiGen.Boolean

import Test.QuickCheck

test1 :: Gen Int
test1 =
  genInt (ge 5 `TAnd` lt 50)

test1'valid :: Property
test1'valid = forAll test1 $ \x -> x >= 5 && x < 50
