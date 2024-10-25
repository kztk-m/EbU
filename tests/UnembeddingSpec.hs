{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
module UnembeddingSpec (spec) where

import           Test.Hspec
import           Unembedding
import           Unembedding.Env

data STLC env a where
  Var :: Ix env a -> STLC env a
  Lam :: STLC (a : env) b -> STLC env (a -> b)
  App :: STLC env (a -> b) -> STLC env a -> STLC env b

deriving stock instance Show (STLC env a)

equalShVar :: Ix env a -> Ix env' a' -> Bool
equalShVar IxZ IxZ          = True
equalShVar (IxS x) (IxS x') = equalShVar x x'
equalShVar _ _              = False

equalSh :: STLC env a -> STLC env' a' -> Bool
equalSh (Var x) (Var y)           = equalShVar x y
equalSh (Lam e) (Lam e')          = equalSh e e'
equalSh (App e1 e2) (App e1' e2') = equalSh e1 e1' && equalSh e2 e2'
equalSh _ _                       = False

class HSTLC f where
  lam :: (f a -> f b) -> f (a -> b)
  app :: f (a -> b) -> f a -> f b

instance LiftVariables STLC where
  newtype Var STLC env a = VarIx (Ix env a)
    deriving newtype Variables
  liftVar (VarIx ix) = Var ix

instance HSTLC (EnvI STLC) where
  lam = liftSOn (ol1 :. End) Lam
  app = liftFO2 App

fromHOAS :: (forall f. HSTLC f => f a) -> STLC '[] a
fromHOAS = runClose

sHOAS :: HSTLC f => f ((a -> b -> c) -> (a -> b) -> a -> c)
sHOAS = lam $ \x -> lam $ \y -> lam $ \z -> x `app` z `app` (y `app` z)

sTerm :: STLC '[] ((a -> b -> c) -> (a -> b) -> a -> c)
sTerm = Lam $ Lam $ Lam $ Var i2 `App` Var i0 `App` (Var i1 `App` Var i0)
  where
    i0 = IxZ
    i1 = IxS i0
    i2 = IxS i1

spec :: Spec
spec = do
  describe "runClose" $
    it "converts the S-combinator correctly" $
      fromHOAS sHOAS `shouldSatisfy` equalSh sTerm

