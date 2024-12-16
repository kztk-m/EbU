{-# LANGUAGE TypeApplications #-}
module Unembedding.EnvSpec (spec) where

import           Data.Coerce           (coerce)
import           Data.Functor.Identity (Identity (..))
import           Test.Hspec
import           Unembedding.Env

spec :: Spec
spec = do
  describe "Unembedding.Env.fromFunc" $ do
    it "can convert nullary function" $ do
      fromFunc (Identity 42) ENil `shouldBe` Identity (42 :: Int)
    it "can convert unary function" $ do
      let b = True
      fromFunc (coerce @(Bool -> Bool) @(Identity Bool -> Identity Bool) not) (ECons (Identity b) ENil) `shouldBe` Identity (not b)
    it "can convert binary function" $ do
      let n1 = 42
      let n2 = 36
      fromFunc (coerce @(Int -> Int -> Int) @(Identity Int -> Identity Int -> Identity Int) (+))
               (ECons (Identity n1) $ ECons (Identity n2) ENil)
               `shouldBe` Identity (n1 + n2)

