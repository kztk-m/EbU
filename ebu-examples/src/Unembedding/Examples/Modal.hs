{-
Taken from Sections 2 in:

    R. Davies & F Pfenning: A Modal Analysis of Staged Computation, JACM 2001.

The use of EbU in this implementation is tricker because it violates its
assumption about target languages. A typing context at which a variable is bound
must be no larger than any typing context at which the variable is used.

Fortunately, this violation will not cause any issue because, in this particular
system, the semantics of such a variable (more specifically, ones introduced by
"let box") is NOT indexed by a typing context.
-}

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -Wno-missing-export-lists #-}


module Unembedding.Examples.Modal where
import           Unembedding.Env (Env (..), Ix)

import           Data.Kind       (Type)
import           Data.Proxy
import qualified Unembedding     as UE
import qualified Unembedding.Env as UE

data Ty = Ty :~> Ty | O | B Ty

infixr 0 :~>

data ModalL menv oenv a where
  OVar :: Ix oenv a -> ModalL menv oenv a
  Abs  :: ModalL menv (a : oenv) b -> ModalL menv oenv (a :~> b)
  App  :: ModalL menv oenv (a :~> b) -> ModalL menv oenv a -> ModalL menv oenv b

  MVar :: Ix menv a -> ModalL menv oenv a
  Box  :: ModalL menv '[] a -> ModalL menv oenv (B a)
  LetB :: ModalL menv oenv (B a) -> ModalL (a : menv) oenv b -> ModalL menv oenv b

deriving stock instance Show (ModalL menv oenv a)

class STLC (e :: Ty -> Type) where
  lam :: (e a -> e b) -> e (a :~> b)
  app :: e (a :~> b) -> e a -> e b

class HModalL (u :: Ty -> Type) e | e -> u where
  mvar :: u a -> e a
  box  :: (forall e'. (STLC e', HModalL u e') => e' a) -> e (B a)
  letb :: e (B a) -> (u a -> e b) -> e b

-- STLC', Box', HModalL' are used for intermediate semantic domains.

class STLC' (e :: ([Ty], Ty) -> Type) where
  ovar' :: Ix env a -> e '(env, a)
  lam'  :: e '(a : env, b) -> e '(env, a :~> b)
  app'  :: e '(env, a :~> b) -> e '(env, a) -> e '(env,  b)

class Box' (e :: ([Ty], Ty) -> Type)  where
  box'  :: e '( '[], a) -> e '(env, B a)

class HModalL' (u :: Ty -> Type) (e :: ([Ty], Ty) -> Type) | e -> u where
  mvar' :: u a -> e '(env, a)
  letb' :: e '(env, B a) -> (u a -> e '(env, b)) -> e '(env,  b)

newtype E (e :: ([Ty], Ty) -> Type) env a = E (e '(env, a))
newtype U (u :: Ty -> Type) (env :: [Ty]) a = U (u a)

-- data C (e :: ([Ty],Ty) -> Type) (env :: [Ty]) (a :: Ty)  where
--   C :: (forall env'. e '( env', a)) -> C e env a

instance STLC' e => UE.LiftVariables (E e) where
  type Var (E e) = UE.Ix
  liftVar = E . ovar'

instance STLC' e => STLC (UE.EnvI (E e)) where
  lam = UE.liftSOn (UE.ol1 :. UE.ENil) lamSem
    where
      lamSem :: E e (a : env) b -> E e env (a :~> b)
      lamSem (E e) = E $ lam' e
  app = UE.liftFO2 (\(E e1) (E e2) -> E (app' e1 e2))

instance UE.Weakenable (U u) where
  weaken (U u) = U u
  -- Trick. See the NOTE below.
  weakenMany _ _ (U u) = U u

instance (HModalL' u e, STLC' e, Box' e) => HModalL (UE.EnvI (U u)) (UE.EnvI (E e)) where
  mvar = UE.liftFO1' (\(U u) -> E $ mvar' u)

  -- [NOTE] The polymorphic nature of `e` of `box e` prevents the error caused
  -- by `weakenMany` used inside the implementation of `lam`. All variables used
  -- inside `e` must be ones introduced its inside. However, it may happen that
  -- u-variables introduced outside can be used inside `e`. Here comes the
  -- tricky part. This does affects `weakenMany` called in the implementation of
  -- `letb` below, but `weakenMany` for `U u` is defined so that it succeeds
  -- regardless of the typing environments given to it.
  --
  -- This is NOT something embedding-by-unembedding guarantees. Calling
  -- `runClose` not for fully-polymorphic expressions (in our case, having type
  -- `forall u e. (STLC e, HModalL u e) => e a`) is dangerous in general.
  box e = UE.EnvI $ \_ -> E $ box' $ let E x = UE.runClose e in x
  letb = UE.liftSOnGen (UE.ol0 :. UE.DimNested (UE.K UE.E):. UE.ENil) (Proxy :: Proxy (E e)) letBSem
    where
      letBSem :: E e env (B a) -> (U u env a -> E e env b) -> E e env b
      letBSem (E e) f = E (letb' e $ \u -> let E res = f (U u) in res)


-- instance UE.LiftVariables (C e) where
--   type Var (C e) = UE.Ix
--   liftVar ix = C $ error "Cannot happen?"

-- instance STLC' e => STLC (UE.EnvI (C e)) where
--   lam = UE.liftSOn (UE.ol1 :. ENil) $ \(C e) -> C $ lam' e
--   app = UE.liftFO2 (\(C e1) (C e2) -> C (app' e1 e2))


-- instance (HModalL' u e, STLC' e, Box' e) => HModalL (UE.EnvI (U u)) (UE.EnvI (C e)) where
--   mvar = UE.liftFO1' (\(U u) -> C $ mvar' u)
--   box = UE.liftFO1' (\(C e) -> C $ box' e)
--   letb = UE.liftSOnGen (UE.ol0 :. UE.DimNested (UE.K UE.E):. UE.ENil) (Proxy :: Proxy (E e)) letBSem
--     where
--       letBSem :: C e env (B a) -> (U u env a -> C e env b) -> C e env b
--       letBSem (C e) f = C (letb' e $ \u -> let C res = f (U u) in res)

type family Fst (a :: (k , k')) :: k where
  Fst '(a , b) = a

type family Snd (a :: (k , k')) :: k' where
  Snd '(a , b) = b

newtype WrapL menv oenva = WrapL (ModalL menv (Fst oenva) (Snd oenva))


instance STLC' (UE.EnvI WrapL) where
  ovar' ix = UE.liftFO0 $ WrapL $ OVar ix
  lam' = UE.liftFO1 $ \(WrapL e) -> WrapL $ Abs e
  app' = UE.liftFO2 $ \(WrapL e1) (WrapL e2) -> WrapL $ App e1 e2

instance Box' (UE.EnvI WrapL) where
  box' = UE.liftFO1 $ \(WrapL e) -> WrapL $ Box e

instance HModalL' (UE.EnvI Ix) (UE.EnvI WrapL) where
  mvar' = UE.liftFO1' $ \ix -> WrapL $ MVar ix
  letb' = UE.liftSOn' (UE.ol0 :. UE.ol1 :. ENil) Proxy $ \(WrapL e1) (WrapL e2) -> WrapL $ LetB e1 e2

convert :: forall a. (forall e u. (STLC e, HModalL u e) => e a) -> ModalL '[] '[] a
convert h =
  let h' :: forall e' u'. (STLC' e', Box' e', HModalL' u' e') => e' '( '[], a)
      h' = let E x = UE.runClose (h :: UE.EnvI (E e') a) in x
  in let WrapL ex = UE.runClose h' in ex

ex0 :: (STLC e, HModalL u e) => e (B a :~> B (B a))
ex0 = lam $ \x -> letb x $ \u -> box (box $ mvar u)


ex1 :: forall u e a1 a2. (STLC e, HModalL u e) => e (B (a1 :~> a2) :~> (B a1 :~> B a2))
ex1 = lam $ \x -> lam $ \y -> letb x $ \u -> letb y $ \v -> box (app (mvar u) (mvar v))

ex2 :: (STLC e, HModalL u e) => e (B b :~> b)
ex2 = lam $ \x -> letb x $ \u -> mvar u

ex3 :: HModalL u e => e (B (b :~> b))
ex3 = box $ lam $ \x -> x

-- >>> convert ex0
-- Abs (LetB (OVar IxZ) (Box (Box (MVar IxZ))))
-- >>> convert ex1
-- Abs (Abs (LetB (OVar (IxS IxZ)) (LetB (OVar IxZ) (Box (App (MVar (IxS IxZ)) (MVar IxZ))))))
-- >>> convert ex2
-- Abs (LetB (OVar IxZ) (MVar IxZ))
-- >>> convert ex3
-- Box (Abs (OVar IxZ))
