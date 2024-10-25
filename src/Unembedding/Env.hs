{-

Generic environment used by Embedding by Unembedding, and functions over it.

-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
module Unembedding.Env (
  Env(..), Ix(..), lookEnv, lenEnv, mapEnv,
  Append, appendEnv,

  Func, fromFunc,
  ) where
import           Data.Kind (Type)

-- | A generic environment
--   What this is an env of can be customised by the selection of f
--     f := Proxy => Type env (no values stored in env)
--     f := Maybe => value env, where we might not have all assignments
data Env (f :: k -> Type) (as :: [k]) where
  ENil  :: Env f '[]
  ECons :: f a -> Env f as -> Env f (a ': as)

-- | (typed) de Bruijn indices witness that a is in env
data Ix (as :: [k]) (a :: k) where
  IxZ :: Ix (a ': as) a             -- At element in question.
  IxS :: Ix as a -> Ix (b ': as) a  -- Element lies further into the env.

deriving stock instance Show (Ix as a)


-- | Looking up something in an env using Ix
lookEnv :: Env f as -> Ix as a -> f a
lookEnv env0 IxZ = case env0 of
  ECons v _ -> v
lookEnv env0 (IxS n) = case env0 of
  ECons _ env -> lookEnv env n

-- | Finds the length of an env
lenEnv :: Env f as -> Int
lenEnv ENil         = 0
lenEnv (ECons _ as) = 1 + lenEnv as

-- examplef :: (forall x . Proxy x -> Maybe x)
-- examplef _ = Nothing

-- | Changes what sort of env we have
-- e.g. we could use this to go from a ProxyEnv to a MaybeEnv with (const Nothing)
mapEnv :: (forall x. f x -> g x) -> Env f as -> Env g as
mapEnv _ ENil         = ENil
mapEnv f (ECons x xs) = ECons (f x) (mapEnv f xs)

-- | Append for type level lists
type family Append as bs where
  Append '[] bs = bs
  Append (a ': as) bs = a ': Append as bs

appendEnv :: Env f as -> Env f bs -> Env f (Append as bs)
appendEnv ENil ys         = ys
appendEnv (ECons x xs) ys = ECons x (appendEnv xs ys)

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


fromFunc :: Func sem as (sem r) -> Env sem as -> sem r
fromFunc e ENil         = e
fromFunc e (ECons a as) = fromFunc (e a) as
