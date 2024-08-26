module TTKVSpec (spec) where

import Data.IntSet qualified as IS
import Data.Map.Strict qualified as M
import Skeletest
import Skeletest.Prop.Gen qualified as Gen
import Skeletest.Prop.Range qualified as Range
import TTKV

spec :: Spec
spec = do
    describe "new" $ do
        it "is initially empty" $ do
            let ttkv = new @String @String 0
            _started ttkv `shouldBe` 0
            _mapping ttkv `shouldBe` M.empty
            times ttkv `shouldBe` IS.empty
    describe "newIO" $ do
        it "is initially empty" $ do
            ttkv <- newIO @String @String
            _mapping ttkv `shouldBe` M.empty
            times ttkv `shouldBe` IS.empty
    prop "single get" $ do
        k <- forAll genKey
        v <- forAll genVal
        t <- forAll genTime
        let ttkv = put t k v (new 0)
        (IS.size . times $ ttkv) `shouldBe` 1
    prop "two gets with different keys" $ do
        k1 <- forAll genKey
        k2 <- forAll $ Gen.filter (/= k1) genKey
        v1 <- forAll genVal
        v2 <- forAll genVal
        t1 <- forAll genTime
        t2 <- forAll $ Gen.filter (> t1) genTime
        let ttkv = put t2 k2 v2 $ put t1 k1 v1 (new 0)
        (IS.size . times $ ttkv) `shouldBe` 2
        get Nothing k1 ttkv `shouldBe` Just v1
        get Nothing k2 ttkv `shouldBe` Just v2
    prop "two gets with the same key" $ do
        k <- forAll genKey
        v1 <- forAll genVal
        v2 <- forAll $ Gen.filter (/= v1) genVal
        t1 <- forAll genTime
        t2 <- forAll $ Gen.filter (> t1) genTime
        let ttkv = put t2 k v2 $ put t1 k v1 (new 0)
        (IS.size . times $ ttkv) `shouldBe` 2
        get Nothing k ttkv `shouldBe` Just v2
    prop "middle get" $ do
        k <- forAll genKey
        v1 <- forAll genVal
        v2 <- forAll $ Gen.filter (/= v1) genVal
        t1 <- forAll genTime
        t2 <- forAll $ Gen.filter (> t1) genTime
        let ttkv = put t2 k v2 $ put t1 k v1 (new 0)
        let delta = (t2 - t1) `div` 2
        (IS.size . times $ ttkv) `shouldBe` 2
        get (Just $ t1 + delta) k ttkv `shouldBe` Just v1
    prop "before time" $ do
        k <- forAll genKey
        v <- forAll genVal
        t <- forAll genTime
        t0 <- forAll $ Gen.filter (< t) genTime
        let ttkv = put t k v (new 0)
        (IS.size . times $ ttkv) `shouldBe` 1
        get (Just t0) k ttkv `shouldBe` Nothing

genTime :: Gen Int
genTime = Gen.int $ Range.linear 1 1000

genKey :: Gen String
genKey = Gen.string (Range.linear 1 100) Gen.unicode

genVal :: Gen String
genVal = genKey
