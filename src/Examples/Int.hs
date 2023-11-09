-- |

module Examples.Int where

import ValiGen.Refine
import ValiGen.Primitive

import Test.QuickCheck

test1 :: Gen Int
test1 = refined (ge 5 /\ lt 50)

test1'valid :: Property
test1'valid = forAll test1 $ \x -> x >= 5 && x < 50

test1'filter :: Property
test1'filter = forAll (choose (minBound, maxBound)) $ \(x :: Int) ->
  (x >= 5 && x < 50) ==> True :: Property

test2 :: Gen (Int, Int)
test2 = undefined

test3 :: Gen Int
test3 =
  refined ((ge 5 /\ lt 50)
            \/
           gt (maxBound - 20))

test3'valid :: Property
test3'valid = forAll test3 $ \x -> (x >= 5 && x < 50) || x > maxBound - 20
