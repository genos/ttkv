{-# LANGUAGE TemplateHaskell #-}

module Main where

import Data.IntSet qualified as IS
import Data.Map.Strict qualified as M
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import System.Exit (exitFailure)
import TTKV qualified as T

genTime :: Gen Int
genTime = Gen.int $ Range.linear 1 1000

genKey :: Gen String
genKey = Gen.string (Range.linear 1 100) Gen.unicode

genVal :: Gen String
genVal = genKey

prop_newIsEmpty :: Property
prop_newIsEmpty = property $ do
    let ttkv = T.new @String @String 0
    T._started ttkv === 0
    T._mapping ttkv === M.empty

prop_singleGet :: Property
prop_singleGet = property $ do
    k <- forAll genKey
    v <- forAll genVal
    t <- forAll genTime
    let ttkv = T.put t k v (T.new 0)
    IS.size (T.times ttkv) === 1

prop_TwoGetsDiffKeys :: Property
prop_TwoGetsDiffKeys = property $ do
    k1 <- forAll genKey
    k2 <- forAll $ Gen.filter (/= k1) genKey
    v1 <- forAll genVal
    v2 <- forAll genVal
    t1 <- forAll genTime
    t2 <- forAll $ Gen.filter (> t1) genTime
    let ttkv = T.put t2 k2 v2 $ T.put t1 k1 v1 (T.new 0)
    (IS.size . T.times $ ttkv) === 2
    T.get Nothing k1 ttkv === Just v1
    T.get Nothing k2 ttkv === Just v2

prop_TwoGetsSameKey :: Property
prop_TwoGetsSameKey = property $ do
    k <- forAll genKey
    v1 <- forAll genVal
    v2 <- forAll $ Gen.filter (/= v1) genVal
    t1 <- forAll genTime
    t2 <- forAll $ Gen.filter (> t1) genTime
    let ttkv = T.put t2 k v2 $ T.put t1 k v1 (T.new 0)
    (IS.size . T.times $ ttkv) === 2
    T.get Nothing k ttkv === Just v2

prop_MiddleGet :: Property
prop_MiddleGet = property $ do
    k <- forAll genKey
    v1 <- forAll genVal
    v2 <- forAll $ Gen.filter (/= v1) genVal
    t1 <- forAll genTime
    t2 <- forAll $ Gen.filter (> t1) genTime
    let ttkv = T.put t2 k v2 $ T.put t1 k v1 (T.new 0)
    let delta = (t2 - t1) `div` 2
    (IS.size . T.times $ ttkv) === 2
    T.get (Just $ t1 + delta) k ttkv === Just v1

prop_BeforeTime :: Property
prop_BeforeTime = property $ do
    k <- forAll genKey
    v <- forAll genVal
    t <- forAll genTime
    t0 <- forAll $ Gen.filter (< t) genTime
    let ttkv = T.put t k v (T.new 0)
    (IS.size . T.times $ ttkv) === 1
    T.get (Just t0) k ttkv === Nothing

main :: IO ()
main = do
    result <- checkParallel $$(discover)
    if result
        then putStrLn "All tests passed!"
        else exitFailure
