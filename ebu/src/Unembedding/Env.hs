{-

Generic environment used by Embedding by Unembedding, and functions over it.

-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
module Unembedding.Env (
  Env, pattern ENil, pattern ECons, Ix(..), lookEnv, lenEnv, mapEnv, mapEnvWithIx, pattern (:.), fromIndexer,
  Append, appendEnv,

  Func, fromFunc,
  ) where
import           Data.Kind (Type)

data Env_ (f :: k -> Type) (as :: [k]) where
  ENil_  :: Env_ f '[]
  ECons_ :: !(f a) -> !(Env_ f as) -> Env_ f (a ': as)

-- | A generic environment. One can think this datatype is defined as:
--
--  > data Env f as where
--  >   ENil  :: Env f '[]
--  >   ECons :: !(f a) -> !(Env f as) -> Env f (a : as)
--
--  with constructors 'ENil' and 'ECons'.
--
--   What this is an env of can be customised by the selection of f
--     f := Proxy => Type env (no values stored in env)
--     f := Maybe => value env, where we might not have all assignments
data Env (f :: k -> Type) (as :: [k]) = MkEnv {-# UNPACK #-} !Int !(Env_ f as) -- caches lenEnv

getEnvBody :: Env f as -> Env_ f as
getEnvBody (MkEnv _ es) = es

pattern ENil :: () => (as ~ '[]) => Env f as
pattern ENil <- MkEnv _ ENil_
  where
    ENil = MkEnv 0 ENil_

pattern ECons :: () => (as ~ a1 : as1) => f a1 -> Env f as1 -> Env f as
pattern ECons e es <- MkEnv n (ECons_ e (MkEnv (n-1) -> es))
  where
    ECons e es = MkEnv (lenEnv es + 1) (ECons_ e (getEnvBody es))

-- | infix version of 'ECons'
pattern (:.) :: () => (as ~ a1 : as1) => f a1 -> Env f as1 -> Env f as
pattern e :. es = ECons e es

infixr 4 :.


#if __GLASGOW_HASKELL__ >= 902
{-# INLINABLE ENil #-}
{-# INLINABLE ECons #-}
#endif

{-# COMPLETE ENil, ECons #-}
{-# COMPLETE ENil, (:.) #-}

-- >>> lenEnv $ ECons [1] $ ECons [2] $ ENil
-- 2
-- >>> lenEnv $ ENil
-- 0

-- >>> let ECons _ xs = ECons [1] $ ECons [2] $ ENil
-- >>> lenEnv xs
-- 1

-- | (typed) de Bruijn indices witness that a is in env
data Ix (as :: [k]) (a :: k) where
  IxZ :: Ix (a ': as) a             -- At element in question.
  IxS :: !(Ix as a) -> Ix (b ': as) a  -- Element lies further into the env.

deriving stock instance Show (Ix as a)


-- | Looking up something in an env using Ix
lookEnv :: Env f as -> Ix as a -> f a
lookEnv (MkEnv _ xs) = lookEnv_ xs

lookEnv_ :: Env_ f as -> Ix as a -> f a
lookEnv_ env0 IxZ = case env0 of
  ECons_ v _ -> v
lookEnv_ env0 (IxS n) = case env0 of
  ECons_ _ env -> lookEnv_ env n


-- | Finds the length of an env
lenEnv :: Env f as -> Int
lenEnv (MkEnv len _) = len

-- | Changes what sort of env we have
-- e.g. we could use this to go from a ProxyEnv to a MaybeEnv with (const Nothing)
mapEnv :: (forall x. f x -> g x) -> Env f as -> Env g as
mapEnv f0 (MkEnv n es) = MkEnv n (mapEnv_ f0 es)

mapEnv_ :: (forall x. f x -> g x) -> Env_ f as -> Env_ g as
mapEnv_ _ ENil_         = ENil_
mapEnv_ f (ECons_ x xs) = ECons_ (f x) (mapEnv_ f xs)

-- | A variant of 'mapEnv' with index.
mapEnvWithIx :: (forall x. Ix as x -> f x -> g x) -> Env f as -> Env g as
mapEnvWithIx _ ENil         = ENil
mapEnvWithIx f (ECons x xs) = ECons (f IxZ x) (mapEnvWithIx (f . IxS) xs)

fromIndexer :: (forall x. Ix as x -> f x) -> Env proxy as -> Env f as
fromIndexer f = mapEnvWithIx (const . f)

-- | Append for type level lists
type family Append as bs where
  Append '[] bs = bs
  Append (a ': as) bs = a ': Append as bs

-- | Append two 'Env's.
appendEnv :: Env f as -> Env f bs -> Env f (Append as bs)
appendEnv (MkEnv lxs xs) (MkEnv lys ys) = MkEnv (lxs + lys) (appendEnv_ xs ys)

appendEnv_ :: Env_ f as -> Env_ f bs -> Env_ f (Append as bs)
appendEnv_ ENil_ ys         = ys
appendEnv_ (ECons_ x xs) ys = ECons_ x (appendEnv_ xs ys)

-- | @Func f [a1,...an] r = f a1 -> ... -> f an -> r@
type family Func sem as r where
  Func sem '[] r       = r
  Func sem (a ': as) r = sem a -> Func sem as r

-- | Converts n-ary functions to a unary function on `Env`.
--
-- >>> fromFunc (++) (ECons [1,2] (ECons [3,4] ENil))
-- [1,2,3,4]
-- >>> import Data.Functor.Identity
-- >>> runIdentity $ fromFunc (\(Identity x) -> Identity $ 2^x) (ECons (Identity (4 :: Int)) ENil)
-- 16
-- >>> import Data.Functor.Identity
-- >>> runIdentity $ fromFunc (\(Identity n) (Identity x) -> Identity $ replicate n x) (ECons (Identity 10) (ECons (Identity 'a') ENil))
-- "aaaaaaaaaa"


fromFunc :: Func sem as r -> Env sem as -> r
fromFunc e ENil         = e
fromFunc e (ECons a as) = fromFunc (e a) as
