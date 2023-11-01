module Examples.Primes where

import Test.QuickCheck
import ValiGen.ValiGen
import GHC.Data.BooleanFormula (BooleanFormula)

newtype Prime = Prime { getPrime :: Int }

example1 :: (Check Int, Generate Int)
example1 = (Pred isPrime, Prim (OneOf [2..70]))

example1Normalized :: Generate Int
example1Normalized = uncurry normalizeGenerate example1

example1Gen :: Gen Int
example1Gen = uncurry toGen example1
-- example1 = Filter (Choose (1, 1000)) (Check isPrime)

-- example1 :: ValiGen v Int
-- example1 = Choose (1, 1000) `Intersect` isPrime

-- example2 :: ValiGen v Int
-- example2 = (isPrime `Union` isEven) `Implies` \_ ->
--   OneOf [2]

-- isEven :: ValiGen v Int
-- isEven = mkBasic even (elements [2,4..])

-- isPrime :: ValiGen v Int
-- isPrime = Check isPrime'helper

isPrime :: Int -> Bool
isPrime x = go [2 .. floor (sqrt @Double (fromIntegral x))]
  where
    go = all ((> 0) . (x `mod`))

-- -- isPrime :: ValiGen v Int
-- -- isPrime = Implies (Choose (2, 1000)) $ \x ->
-- --   Check undefined
