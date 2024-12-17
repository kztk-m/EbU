{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
module UnembeddingSpec (spec) where

import           Data.Proxy      (Proxy (..))
import           Test.Hspec
import           Unembedding
import           Unembedding.Env

data STLC env a where
  Var :: Ix env a -> STLC env a
  Lam :: STLC (a : env) b -> STLC env (a -> b)
  App :: STLC env (a -> b) -> STLC env a -> STLC env b

data STLCS env a where
  Ret :: STLC env a -> STLCS env a
  Let :: STLCS env a -> STLCS (a : env) b -> STLCS env b
  Put :: String -> STLCS env () -- something looks-like statement


deriving stock instance Show (STLC env a)
deriving stock instance Show (STLCS env a)

equalShVar :: Ix env a -> Ix env' a' -> Bool
equalShVar IxZ IxZ          = True
equalShVar (IxS x) (IxS x') = equalShVar x x'
equalShVar _ _              = False

equalSh :: STLC env a -> STLC env' a' -> Bool
equalSh (Var x) (Var y)           = equalShVar x y
equalSh (Lam e) (Lam e')          = equalSh e e'
equalSh (App e1 e2) (App e1' e2') = equalSh e1 e1' && equalSh e2 e2'
equalSh _ _                       = False

equalShS :: STLCS env a -> STLCS env' a' -> Bool
equalShS (Ret e) (Ret e')          = equalSh e e'
equalShS (Let s1 s2) (Let s1' s2') = equalShS s1 s1' && equalShS s2 s2'
equalShS (Put str) (Put str')      = str == str'
equalShS _ _                       = False


class HSTLC f where
  lam :: (f a -> f b) -> f (a -> b)
  app :: f (a -> b) -> f a -> f b

class HSTLC f => HSTLCS f s | s -> f where
  ret  :: f a -> s a
  let_ :: s a -> (f a -> s b) -> s b
  put  :: String -> s ()

instance LiftVariables STLC where
  type Var STLC = Ix
  liftVar = Var

instance HSTLC (EnvI STLC) where
  lam = liftSOn (ol1 :. ENil) Lam
  app = liftFO2 App

instance HSTLCS (EnvI STLC) (EnvI STLCS) where
  ret = liftFO1' Ret
  let_ = liftSOn' (ol0 :. ol1 :. ENil) (Proxy @STLC) Let
  put s = liftFO0' (Put s)


fromHOAS :: (forall f. HSTLC f => f a) -> STLC '[] a
fromHOAS = runClose

fromHOASS :: (forall f s. HSTLCS f s => s a) -> STLCS '[] a
fromHOASS = runClose'


sHOAS :: HSTLC f => f ((a -> b -> c) -> (a -> b) -> a -> c)
sHOAS = lam $ \x -> lam $ \y -> lam $ \z -> x `app` z `app` (y `app` z)

sTerm :: STLC env ((a -> b -> c) -> (a -> b) -> a -> c)
sTerm = Lam $ Lam $ Lam $ Var i2 `App` Var i0 `App` (Var i1 `App` Var i0)
  where
    i0 = IxZ
    i1 = IxS i0
    i2 = IxS i1

hwHOAS :: HSTLCS f s => s ((a -> b -> c) -> (a -> b) -> a -> c)
hwHOAS = let_ (put "Hello") $ const $ let_ (put "World") $ const (ret sHOAS)

hwTerm :: STLCS '[] ((a -> b -> c) -> (a -> b) -> a -> c)
hwTerm = Let (Put "Hello") $ Let (Put "World") $ Ret sTerm

spec :: Spec
spec = do
  describe "runClose" $ do
    it "converts the S-combinator correctly" $
      fromHOAS sHOAS `shouldSatisfy` equalSh sTerm
    it "converts statements correctly" $
      fromHOASS hwHOAS `shouldSatisfy` equalShS hwTerm
