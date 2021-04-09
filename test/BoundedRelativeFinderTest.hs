{-# language OverloadedStrings #-}
{-# language BlockArguments #-}

module Main (main) where

import Control.Monad
import Data.Hashable
import Data.List
import Data.Graph(Forest, Tree(..))
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Debug.Trace

import Data.BoundedRelativeFinder

--
zeroDistance :: (Eq a, Ord a, Hashable a, Show a) => Gen a -> Shrink a -> Property
zeroDistance g d = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  let dict = buildShrinkDict d 0 (zip [0..] xs)
  assert $ all (\x -> sort ((xs !!) <$> concat (queryD d 0 dict x)) == sort (filter (== x) xs)) xs

genTree :: Gen a -> Gen (Tree a)
genTree g =
  Gen.recursive Gen.choice
    [ Node <$> g <*> pure [] ]
    [ Node <$> g <*> Gen.list (Range.linear 1 3) (genTree g) ]

shrinkTriangular :: (Show a, Eq a) => Gen a -> Shrink a -> Property
shrinkTriangular g ray = withDiscards 500 $ property $ do
  elems <- shrink ray <$> forAll g
  guard (length elems >= 2)
  assert $ and
    [not (null (shrink ray e1 `intersect` shrink ray e2)) | e1 <- elems, e2 <- elems, e1 /= e2]

main :: IO ()
main =
  () <$ checkParallel (Group "symmetric-relative-finder"
    [ ("values with zero distance are equal",
        zeroDistance (Gen.string (Range.linear 0 4) Gen.alpha) (shrinkListEverywhere emptyShrink))
    , ("shrinkListEverywhere on atomic ints is triangular",
        shrinkTriangular (Gen.list (Range.linear 0 4) (Gen.int (Range.linear (-10) 10))) (shrinkListEverywhere emptyShrink))
    , ("shrinkListEverywhere on shrinkable ints is triangular",
        shrinkTriangular (Gen.list (Range.linear 0 4) (Gen.int (Range.linear (-10) 10))) (shrinkListEverywhere (shrinkStepTo 1 0)))
    , ("shrinkListEverywhere on strings is triangular",
        shrinkTriangular (Gen.string (Range.linear 0 4) Gen.alpha) (shrinkListEverywhere emptyShrink))
    , ("shrinkListEverywhere on lists of strings is triangular",
        shrinkTriangular (Gen.list (Range.linear 0 4) (Gen.string (Range.linear 0 4) Gen.alpha)) (shrinkListEverywhere (shrinkListEverywhere emptyShrink)))
    , ("shrinkTree on trees of strings is triangular",
        shrinkTriangular (genTree (Gen.string (Range.linear 0 4) Gen.alpha)) (shrinkTree (shrinkListEverywhere emptyShrink)))
    ])


