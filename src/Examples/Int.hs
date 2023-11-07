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

test1'filter :: Property
test1'filter = forAll (choose (minBound, maxBound)) $ \(x :: Int) ->
  (x >= 5 && x < 50) ==> True :: Property

test2 :: Gen (Int, Int)
test2 =
  genPair (gt 0, \x -> gt x)

test2'valid :: Property
test2'valid = forAll test2 $ \(x, y) -> x > 0 && y > x
