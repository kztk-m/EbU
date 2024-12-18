{-

Embedding of a simple first-order language with the fix-point operator.

-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Unembedding.Examples.FirstOrder where
import           Data.Proxy      (Proxy (..))
import qualified Unembedding     as UE
import qualified Unembedding.Env as UE
import           Unembedding.Env (Env (..))

data ValType = VInt | VBool
data FunType = I ValType | ValType :~> FunType

infixr 0 :~>

-- First-order de Bruijn representation for a first-order language with fix.
data FOLang fenv venv a where
  FLam :: FOLang fenv (a : venv) b -> FOLang fenv venv (a :~> b)
  FApp :: FOLang fenv venv (a :~> b) -> FOLang fenv venv (I a) -> FOLang fenv venv b
  FVar :: UE.Ix venv a -> FOLang fenv venv (I a)
  FFun :: UE.Ix fenv f -> FOLang fenv venv f
  FFix :: FOLang (f : fenv) venv f -> FOLang fenv venv f

deriving stock instance Show (FOLang fenv venv a)

weakenVar :: Proxy b -> Proxy venv -> UE.Env Proxy as -> UE.Ix (UE.Append as venv) a -> UE.Ix (UE.Append as (b : venv)) a
weakenVar _ _ (_ :. _) UE.IxZ           = UE.IxZ
weakenVar pb pvenv (_ :. as) (UE.IxS x) = UE.IxS (weakenVar pb pvenv as x)
weakenVar _ _ ENil ix                   = UE.IxS ix

weaken2 :: Proxy b -> Proxy venv -> UE.Env Proxy as -> FOLang fenv (UE.Append as venv) a -> FOLang fenv (UE.Append as (b : venv)) a
weaken2 pb pvenv as (FLam e) = FLam $ weaken2 pb pvenv (Proxy :. as) e
weaken2 pb pvenv as (FApp e1 e2) = FApp (weaken2 pb pvenv as e1) (weaken2 pb pvenv as e2)
weaken2 pb pvenv as (FVar ix) = FVar (weakenVar pb pvenv as ix)
weaken2 _ _ _ (FFun ix) = FFun ix
weaken2 pb pvenv as (FFix e) = FFix $ weaken2 pb pvenv as e



-- Its HOAS representation (in tagless-final style)
--
-- Observe that it involves two semantic domains. Also, `lam` and `fix` bind
-- variables from different domains.
class HFOLang i e | e -> i where
  lam :: (i a -> e b) -> e (a :~> b)
  var :: i a -> e (I a)
  app :: e (a :~> b) -> e (I a) -> e b
  fix :: (e a -> e a) -> e a

-- Intermediate type class
class HFOLang' e where
  lam' :: e (a : venv) b -> e venv (a :~> b)
  app' :: e venv (a :~> b) -> e venv (I a) -> e venv b
  var' :: UE.Ix venv a -> e venv (I a)
  fix' :: (e venv a -> e venv a) -> e venv a

-- newtype wrapper for the above e
newtype E e (env :: [ValType]) (a :: FunType) = E { unE :: e env a }

instance UE.Weakenable e => UE.Weakenable (E e) where
  weaken (E x) = E (UE.weaken x)

instance (HFOLang' e, UE.Weakenable e) => HFOLang (UE.EnvI UE.Ix) (UE.EnvI (E e)) where
  lam = UE.liftSOn' @UE.Ix @(E e) (UE.ol1 :. ENil) Proxy $ \(E e) -> E (lam' e)
  app = UE.liftFO2 $ \(E e1) (E e2) -> E (app' e1 e2)
  fix = UE.liftSOnGen @UE.Ix @(E e) (UE.DimNested (UE.K UE.E) :. ENil) (Proxy :: Proxy UE.Ix) $ \f -> E $ fix' (unE . f . E)
  var = UE.liftFO1' $ E . var'

-- type family Fst (a :: (k , k')) :: k where
--   Fst '(a , b) = a

-- type family Snd (a :: (k , k')) :: k' where
--   Snd '(a , b) = b

-- newtype WrapL fenv venva = WrapL (FOLang fenv (Fst venva) (Snd venva))


-- newtype SwFOLang venv fenv a = SwFOLang (FOLang fenv venv a)
newtype Sw f venv fenv a = Sw (f fenv venv a)

newtype Wrap e venv a = Wrap { unWrap :: UE.EnvI (Sw e venv) a }

instance UE.LiftVariables (Sw FOLang venv) where
  type Var (Sw FOLang venv) = UE.Ix
  liftVar ix = Sw $ FFun ix

instance HFOLang' (Wrap FOLang) where
  lam' (Wrap ex) = Wrap $ UE.liftFO1' (\(Sw e) -> Sw $ FLam e) ex
  app' (Wrap ex1) (Wrap ex2) = Wrap $ UE.liftFO2 (\(Sw e1) (Sw e2) -> Sw (FApp e1 e2)) ex1 ex2
  var' ix = Wrap $ UE.liftFO0 $ Sw $ FVar ix
  fix' f = Wrap $ UE.liftSOn (UE.ol1 :. ENil) fixSem (unWrap . f . Wrap)
    where
      fixSem (Sw e) = Sw $ FFix e

instance UE.Weakenable (Wrap FOLang) where
  weaken (Wrap w) = Wrap $ UE.liftFO1' (\(Sw e) -> Sw (weaken2 Proxy Proxy ENil e)) w

convert :: forall a. (forall i e. HFOLang i e => e a) -> FOLang '[] '[] a
convert h =
  let h' :: forall e. (UE.Weakenable e, HFOLang' e) => e '[] a
      h' = unE $ UE.runClose h
      Sw r = UE.runClose (unWrap h') -- TODO: Is it really safe?
  in r

-- >>> convert $ fix (\_ -> lam $ \x -> lam $ \y -> var x)
-- FFix (FLam (FLam (FVar (IxS IxZ))))

-- >>> convert $ lam $ \x -> lam $ \y -> fix (\_ -> lam $ \x -> lam $ \y -> var x) `app` var x `app` var y
-- FLam (FLam (FApp (FApp (FFix (FLam (FLam (FVar (IxS IxZ))))) (FVar (IxS IxZ))) (FVar IxZ)))

-- >>> convert $ fix (\f -> lam $ \x -> app f (var x))
-- FFix (FLam (FApp (FFun IxZ) (FVar IxZ)))
