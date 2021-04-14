{-# language OverloadedStrings #-}
{-# language BlockArguments #-}

module Main (main) where

import Control.Monad
import Data.Hashable
import Data.List
import Data.Graph(Forest, Tree(..))
import qualified Data.Vector.Unboxed as UV
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Debug.Trace

import Data.BoundedRelativeFinder

--
zeroDistance :: (Eq a, Ord a, Hashable a, Show a) => Gen a -> Shrink a -> Property
zeroDistance g d = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  let dict = buildShrinkDict d 0 xs
  assert $ all (\x -> sort ((xs !!) <$> concatMap (UV.toList . snd) (queryD d 0 dict x)) == sort (filter (== x) xs)) xs

genTree :: Gen a -> Gen (Tree a)
genTree g =
  Gen.recursive Gen.choice
    [ Node <$> g <*> pure [] ]
    [ Node <$> g <*> Gen.list (Range.linear 0 4) (genTree g) ]

shrinkTriangular :: (Show a, Eq a) => Gen a -> Shrink a -> Property
shrinkTriangular g ray = withTests 500 $ withDiscards 2000 $ property $ do
  elems <- shrink ray <$> forAll g
  guard (length elems >= 2)
  assert $ and
    [not (null (shrink ray e1 `intersect` shrink ray e2)) | e1 <- elems, e2 <- elems, e1 /= e2]

queryBOrdering ray d dict q = property $ do
  let xs = [(h, d) | (ShrinkAt h d, _) <- queryB ray d (buildShrinkDict ray d dict) q]
  assert (xs == sortOn snd xs)
  assert (length xs > 1)

main :: IO ()
main = do
  checkParallel $ Group "bounded-relative-finder"
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
    , ("shrinkListEverywhere (shrinkListHead) on lists of lists of shrinkable ints is triangular",
        shrinkTriangular (Gen.list (Range.linear 0 4) (Gen.list (Range.linear 0 4) (Gen.int (Range.linear (-10) 10)))) (shrinkListEverywhere (shrinkListHead (shrinkStepTo 1 0))))
    , ("shrinkTree (shrinkListEverywhere) on trees of strings is triangular",
        shrinkTriangular (genTree (Gen.string (Range.linear 0 4) Gen.alpha)) (shrinkTree (shrinkListEverywhere emptyShrink)))
    , ("queryB returns results in order of query shrink depth",
        withTests 1 $ queryBOrdering (shrinkListEverywhere emptyShrink) 3 ["hello", "hey"] "hej")
    ]
  return ()


