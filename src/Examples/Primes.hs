module Examples.Primes where

import Test.QuickCheck
import ValiGen.ValiGen
import GHC.Data.BooleanFormula (BooleanFormula)
import Control.Monad (replicateM)

newtype Prime = Prime { getPrime :: Int }

example1 :: (Check Int, Generate Int)
example1 = (Pred isPrime, Prim (OneOf [2..70]))

example1Normalized :: Generate Int
example1Normalized = uncurry normalizeGenerate example1

example1Gen :: Gen Int
example1Gen = uncurry toGen example1
-- example1 = Filter (Choose (1, 1000)) (Check isPrime)

newtype EvenList = EvenList [Int]
  deriving (Show, Ord, Eq)

-- instance Arbitrary EvenList where
--   arbitrary = example2

example2 :: Gen EvenList
example2 = fmap EvenList $ (`suchThat` ((> 50) . length)) $ resize 100 $ listOf (choose (1, 20))

example2' :: Gen EvenList
example2' = fmap EvenList $ (`suchThat` ((> 50) . length)) $ do
  n <- getSize
  sz <- choose (0, n)
  vectorOf sz (choose (1, 20))

example2'' :: Gen EvenList
example2'' = fmap EvenList $ do
  n <- getSize
  sz <- choose (0, n)
  vectorOf sz (choose (1, 20)) `suchThat` ((> 50) . length)

example2''' :: Gen EvenList
example2''' = fmap EvenList $ do
  n <- getSize
  sz <- choose (0, n) -- TODO: Would like to somehow combine the `suchThat` with this line...
  replicateM sz (choose (1, 20)) `suchThat` ((> 50) . length)

-- choose (0, n) >>= \sz -> f sz `suchThat` ((> 50) . length)
-- choose (0, n) >>= \sz -> With (sz .> 50) (f sz)
--   ^ Needs to run the bind continuation with a dummy variable first, to get constraints?

example2_ :: Gen EvenList
example2_ = fmap EvenList $ do
  xs <- resize 100 $ listOf (choose (1, 20))
  if length xs > 50
    then pure xs
    else discard

easy :: EvenList -> Property
easy (EvenList xs) = even (length xs) ==> True

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
