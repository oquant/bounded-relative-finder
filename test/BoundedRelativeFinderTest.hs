{-# language OverloadedStrings #-}
{-# language BlockArguments #-}

module Main (main) where

import Control.Monad
import Data.Hashable
import Data.List
import Data.Maybe
import Data.Graph(Forest, Tree(..))
import qualified Data.Vector.Unboxed as UV
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Debug.Trace

import Data.BoundedRelativeFinder

--
zeroDistanceD :: (Eq a, Ord a, Hashable a, Show a) => Gen a -> Shrink a -> Property
zeroDistanceD g ray = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  let dict = buildShrinkDict ray 0 xs
  assert $ all (\x -> sort ((xs !!) <$> concatMap (UV.toList . snd) (queryD ray 0 dict x)) == sort (filter (== x) xs)) xs

zeroDistanceB :: (Eq a, Ord a, Hashable a, Show a) => Gen a -> Shrink a -> Property
zeroDistanceB g ray = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  let dict = buildShrinkDict ray 0 xs
  assert $ all (\x -> sort ((xs !!) <$> concatMap (UV.toList . snd) (queryB ray 0 dict x)) == sort (filter (== x) xs)) xs

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

validate ray depth (ShrinkAt h qd) result =
  case find (\(ShrinkAt dh _) -> dh == h) (uniqueShrinksBreadth ray depth result) of
    Just (ShrinkAt _ dd) -> Just (qd, dd)
    _ -> Nothing

queryDValid ray depth g = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  x <- forAll g
  let dict = buildShrinkDict ray depth xs
  let qrs = queryD ray depth dict x
  assert $ not $ null qrs
  assert $ all (\(s, rs) -> UV.all (\r -> uncurry max (fromMaybe maxBound $ validate ray depth s (xs !! r)) <= depth) rs) qrs

queryBValid ray depth g = property $ do
  xs <- forAll (Gen.list (Range.linear 0 100) g)
  x <- forAll g
  let dict = buildShrinkDict ray depth xs
  let qrs = queryB ray depth dict x
  assert $ not $ null qrs
  assert $ all (\(s, rs) -> UV.all (\r -> uncurry max (fromMaybe maxBound $ validate ray depth s (xs !! r)) <= depth) rs) qrs

main :: IO ()
main = do
  checkParallel $ Group "bounded-relative-finder"
    [ ("results returned by queryB at zero distance are equal",
        zeroDistanceB (Gen.string (Range.linear 0 4) Gen.alpha) (shrinkListEverywhere emptyShrink))
    , ("results returned by queryD at zero distance are equal",
        zeroDistanceD (Gen.string (Range.linear 0 4) Gen.alpha) (shrinkListEverywhere emptyShrink))
    , ("results returned by queryB are all valid",
        queryBValid (shrinkListEverywhere emptyShrink) 2 (Gen.string (Range.linear 0 4) Gen.alpha))
    , ("results returned by queryD are all valid",
        queryDValid (shrinkListEverywhere emptyShrink) 2 (Gen.string (Range.linear 0 4) Gen.alpha))
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


