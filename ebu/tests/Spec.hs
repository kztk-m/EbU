module Main (main) where

import           Test.Hspec
import           Unembedding.EnvSpec as E
import           UnembeddingSpec     as U

main :: IO ()
main = hspec $ do
  E.spec
  U.spec
