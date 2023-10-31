module Examples.Primes where

import Test.QuickCheck
import ValiGen.ValiGen
import GHC.Data.BooleanFormula (BooleanFormula)

newtype Prime = Prime { getPrime :: Int }

example1 :: ValiGen v Int
example1 = Choose (1, 1000) `Intersect` isPrime

example2 :: ValiGen v Int
example2 = (isPrime `Union` isEven) `Implies` \_ ->
  OneOf [2]

isEven :: ValiGen v Int
isEven = mkBasic even (elements [2,4..])

isPrime :: ValiGen v Int
isPrime = Check isPrime'helper

isPrime'helper :: Int -> Bool
isPrime'helper x = go [2 .. floor (sqrt @Double (fromIntegral x))]
  where
    go = all ((> 0) . (`mod` x))

-- isPrime :: ValiGen v Int
-- isPrime = Implies (Choose (2, 1000)) $ \x ->
--   Check undefined
