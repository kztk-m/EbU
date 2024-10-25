{- |

Contains unembedding framework to support using the Embedding by Unembedding technique.

-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE FlexibleContexts       #-}

module Unembedding
  (
    -- * Interface Typeclass
    LiftVariables(..), Variables (..),

    -- * Interpretation of open terms
    --
    -- | The @run***@ functions must be used with polymorphic arguments, like
    --  @forall f. HOAS f => f a@ and @forall f. HOAS f => f a -> f b@, where @HOAS@ is
    --  a user-defined finally-tagless HOAS interface. Otherwise, they may cause errors.
    TEnv, EnvI(..), runOpen, runOpenN, runClose,
    Nat(..), SNat(..), Vec(..), runOpenV, Repeat,

    -- * Lifting functions for first-order language constructs
    liftFO,
    liftFO0, liftFO1, liftFO2,

    -- * Lifting functions for second-order language constructs
    OfLength(..), ol0, ol1, ol2, ol3, ol4,
    FuncTerm, FuncU, Dim(..),
    liftSOn,

    -- * Internal datatypes and functions used in 'liftSOn'.
    --
    -- | They are supposed to be used typically when a construct is variadic.
    Sig2(..), TermRep(..), URep(..),
    liftSO,

    -- * Internal Manipulation of Variables
    weakenMany,
    var0, var1, var2,

  ) where

import           Data.Functor.Identity (Identity)
import           Data.Kind             (Type)
import           Data.Proxy            (Proxy (..))
import           Unsafe.Coerce         (unsafeCoerce)

import           Unembedding.Env

-- useful envs
type VEnv     = Env Identity -- Value environment.
type EEnv exp = Env exp      -- Expression environment.
type TEnv     = Env Proxy    -- Type environment.

type REnv     = Env Maybe    -- Result of reverse computation.

-- | Defines semantics that can be unembed: those that have an environment that can
--   focus on a variable, and be weakened
class Variables (semvar :: [k] -> k -> Type) where
  var    :: semvar (a ': as) a
  weaken :: semvar as a -> semvar (b ': as) a

-- | Ix is a free Variables.
instance Variables Ix where
  var = IxZ
  weaken = IxS

-- | Generic weakening
--   Compares two environments and repeatedly applies 'weaken' to unify them
--   While it appears partial, it is guaranteed to work by the original unembedding work.
-- weaken + compare
weakenMany :: Variables semvar => TEnv as -> TEnv as' -> semvar as b -> semvar as' b
weakenMany e1 e2 = go lenDiff e1 e2
  where
    l1 = lenEnv e1
    l2 = lenEnv e2
    lenDiff = l2 - l1
    go :: forall sem as as' b. Variables sem => Int -> TEnv as -> TEnv as' -> sem as b -> sem as' b
    go 0 _   _             ls = unsafeCoerce ls
    go n e1' (ECons _ e2') ls = weaken $ go (n-1) e1' e2' ls
    go _ _    _            _  = error $ "weakenMany: the first argument (len: " ++ show l1 ++  ") is smaller than the second (lens: " ++ show l2 ++ ")"

-- Handy functions for getting the semantics to focus on a particular variable in its env
-- Defined as a combo of 'var' and 'weaken'

var0 :: Variables semvar => semvar (a : env) a
var0 = var

var1 :: Variables semvar => semvar (b : a : s) a
var1 = weaken var0

var2 :: Variables semvar => semvar (b2 : b1 : a : s) a
var2 = weaken var1

-- | Typeclass to capture the ability to lift semantics of variables (values?)
-- into semantics of terms.
--
-- [NOTE] This is a deviation from our ICFP 2023 paper. We find this is handy
-- when we apply EbU for the original unembedding (i.e., conversion to de Bruijn
-- terms); it is typically easy to provide a Variables instance for just
-- variables rather than terms. The latter requires us to weaken variables that
-- appear in the middle of an environment.
class Variables (Var sem) => LiftVariables (sem :: [k] -> k -> Type) where
  -- | Semantics of variables. Definitions like
  -- @
  -- newtype Var Sem env a = SemIx (Ix env a)
  -- @
  -- always works as 'Ix' is the free instance of Variables. Another typical implementation is
  -- @
  -- newtype Var Sem env a = IdentitySem (Sem env a)
  -- @
  -- which works when 'Sem' is an instance of 'Variables'.
  data Var sem (env :: [k]) (a :: k) :: Type
  liftVar :: Var sem env a -> sem env a

-- Wrapper the quantifies over env so that our type can only have one param like the HOAS
-- Called EnvI, short for EnvIndexed, as it is indexed by an environment
newtype EnvI sem a = EnvI { runEnvI :: forall as. TEnv as -> sem as a }

-- | Interprets an open hoas term, expressed as a function, as the semantic domain
--   where there is only one variable in the env (the variable made by the arg to the hoas term)
-- NOTE:- while the hoas term is a function with one arg, there is no guarentee
--        that it represents a term with a single variable
--        This is because this hoas term is not limited to only use the semantics
--        of the language in question, atm it has all of haskell to mess things up
--        When using this, you want to define a wrapper specific to your language
--        e.g.
--          runOpenILC :: (forall e. ILChaos e => e a -> e b) -> ILC '[a] b
--          runOpenILC f = runOpen f
--        to ensure no funny business goes on
runOpen :: LiftVariables sem => (EnvI sem a -> EnvI sem b) -> sem '[a] b
runOpen f = let eA = ECons Proxy ENil
                x  = EnvI $ \e' -> liftVar $ weakenMany eA e' var
            in runEnvI (f x) eA

-- | Same vibe as runOpen just with N free variables, represented as type env
runOpenN :: LiftVariables sem => TEnv as -> (Env (EnvI sem) as -> EnvI sem a) -> sem as a
runOpenN e f =
  -- exactly the same as runOpen, we need to make the arg to f, apply it and unpack the result
  -- just this time our arg is an env of EnvI sem terms
  let xs = mkXs e -- make arg
  in runEnvI (f xs) e -- apply f, unpack result
  where
    -- make env of terms using type env
    mkXs :: LiftVariables sem => TEnv as' -> Env (EnvI sem) as'
    mkXs ENil = ENil
    mkXs te@(ECons _ te') =
      let x = EnvI $ \e' -> liftVar $ weakenMany te e' var -- each EnvI term is a var term with envs unified
      in ECons x (mkXs te')

-- | A special case of 'runOpenN'
runClose :: LiftVariables sem => EnvI sem a -> sem '[] a
runClose e = runOpenN ENil (const e)

-- Data type representing natural numbers in peano arithmetic pres, ready to be lifted to the type level
data Nat = Z | S Nat

-- A rep of nats that also features a matching type level nat (Nat lifted)
data SNat n where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- "Dependently" typed vector, a vector with the length represented in the type
data Vec a n where
  VecNil  :: Vec a 'Z
  VecCons :: a -> Vec a n -> Vec a ('S n)

-- Type level function that will create type level list full of the same type
-- basically 'repeat' but for type level lists
type family Repeat a n = m | m -> n where
  Repeat a 'Z     = '[]
  Repeat a ('S n) = a ': Repeat a n

-- | runOpenN, but the arg gets passed in as a vec
runOpenV :: forall sem n a b.
            LiftVariables sem => SNat n -> (Vec (EnvI sem a) n -> EnvI sem b) -> sem (Repeat a n) b
runOpenV sn f = runOpenN (mkEnv sn) (f . e2v sn)
  where
    mkEnv :: forall m. SNat m -> TEnv (Repeat a m)
    mkEnv SZ     = ENil
    mkEnv (SS n) = ECons (Proxy :: Proxy a) (mkEnv n)

e2v :: SNat n -> Env e (Repeat a n) -> Vec (e a) n
e2v SZ ENil             = VecNil
e2v (SS n) (ECons a as) = VecCons a (e2v n as)

-- v2e :: Vec (e a) n -> Env e (Repeat a n)
-- v2e VecNil         = ENil
-- v2e (VecCons a as) = ECons a (v2e as)

-- the overall vibes of the lifting functions is that they take an env with some
-- EnvI rep of the terms that belong tot he bound variables and we wanna inline them
-- the bound variables get inlined as var terms, properly referencing a new env that we make and unify with the incoming one
-- then there is the garbage of dealing with the different type formats (e.g. the semantic functions take args not envs, or the HOAS expects certain params etc)
-- the for SO there is the additional complication that the args can have args and we must add these to the env

liftFO :: (forall env. Env (sem env) as -> sem env a) -- generic handling of a semantic function
      -- we are working in EnvI land
       -> Env (EnvI sem) as
       -> EnvI sem a
liftFO f xs = EnvI $ \e -> f (mapEnv (\(EnvI t) -> t e) xs)
  -- deals with wrapping and unwrapping of U, applying f on the inside
                                          -- unpack from EnvI and apply to env
  -- we need to make our (Env (EnvI sem) as) into a (TEnv env) and a (Env (sem env) as) so we can apply f to it
  -- why does f have that type?
  -- well the TEnv is so that our semantic functions can depend on a type env
  -- the Env (sem env) as is the terms that the bound variables go to (the arguments we wanna give to the semantic function)

-- a selection of monomorphic lifting functions, that makes the generic liftFO
-- work on functions not envs
-- all this is doing is creating the function that works with envs that liftFO
-- expects and defining it by unpacking the values from the env and applying the
-- nicer to work with function we want to it

-- NOTE:- we do not define this generically, we only define SO generically, and that
-- superceeds the need for a FO generic one as you can just give ol0 as all dims

liftFO0 :: (forall env. sem env a) -> EnvI sem a
liftFO0 f = liftFO (const f) ENil

liftFO1 :: (forall env. sem env a -> sem env b) -> EnvI sem a -> EnvI sem b
liftFO1 f x = liftFO (\(ECons xx _) -> f xx) (ECons x ENil)

liftFO2 :: (forall env. sem env a -> sem env b -> sem env c) -> EnvI sem a -> EnvI sem b -> EnvI sem c
liftFO2 f x y = liftFO (\(ECons xx (ECons yy _)) -> f xx yy) (ECons x (ECons y ENil))

-- when it comes to second order constructors, now the arguments can have arguments
-- and we need to accommodate for that
-- the following are ways of describing those arguments:

-- describes arguments of second order constructs. Intended to appear at the type level
data Sig2 k = [k] :~> k
            -- args ~> res
            -- (:~> is just the constructor, basically its a construct that stores the list of args and the result)

-- semantic rep of second order args
data TermRep (sem :: [k] -> k -> Type) (env :: [k]) (s :: Sig2 k) where
  TR :: sem (Append as env) b -> TermRep sem env (as ':~> b)
    -- stores a semantic term where the env includes the second order args
    -- each termRep stores a semantic type, where its env is the env plus its args (Append)
    -- and its type is the result type

-- HOAS rep of second order args
-- this is the type we will create from our semantic function,
-- reformatted using a similar system liftFOn
data URep (sem :: [k] -> k -> Type) (s :: Sig2 k) where
  UR :: TEnv as -> (Env (EnvI sem) as -> EnvI sem b) -> URep sem (as ':~> b)
  -- the TEnv is the type of the arguments to the construct
  -- instead of just storing a term, it stores a function from args (stored in an env) to res

-- same format as liftFo, except now instead of just having envs of sem and EnvI sem,
-- we need TermRep and URep
liftSO :: forall sem ss r. LiftVariables sem =>
  (forall env. Env (TermRep sem env) ss -> sem env r)
  -> Env (URep sem) ss -> EnvI sem r
liftSO f ks = EnvI $ \e -> f (mapEnv (conv e) ks)
  where conv :: TEnv env -> URep sem s -> TermRep sem env s
        conv e (UR e1 k) = TR $ cnv e e1 k
        cnv :: TEnv env -> TEnv as -> (Env (EnvI sem) as -> EnvI sem a)
            -> sem (Append as env) a
        cnv e e1 k = let {ex_e = appendEnv e1 e; xs   = mkXs e e1 ex_e}
                     in runEnvI (k xs) ex_e
        mkXs :: TEnv env -> TEnv as' -> TEnv (Append as' env) -> Env (EnvI sem) as'
        mkXs _ ENil _ = ENil
        mkXs p (ECons _ as) te@(ECons _ te')
          = let x = EnvI $ \e' -> liftVar $ weakenMany te e' var
            in ECons x (mkXs p as te')

-- Here down is the type families (leave in appendix)

data OfLength as where
  LZ :: OfLength '[]
  LS :: OfLength as -> OfLength (a ': as)

-- handy short cuts for values:

-- | Smart constructor for an 'OfLength' zero.
ol0 :: OfLength '[]
ol0 = LZ

-- | Smart constructor for an 'OfLength' one.
ol1 :: OfLength '[a]
ol1 = LS LZ

-- | Smart constructor for an 'OfLength' two.
ol2 :: OfLength '[a,b]
ol2 = LS ol1

-- | Smart constructor for an 'OfLength' three.
ol3 :: OfLength '[a,b,c]
ol3 = LS ol2

-- | Smart constructor for an 'OfLength' four.
ol4 :: OfLength '[a,b,c,d]
ol4 = LS ol3

-- Corresponds to (forall env. Env (TermRep sem env) ss -> sem env r)
type family FuncTerm (sem :: [k] -> k -> Type) (env :: [k])
                     (ss :: [Sig2 k]) (r :: k) | r -> sem env r where
  FuncTerm sem env '[] r = sem env r
  FuncTerm sem env ((as ':~> a) ': ss) r = sem (Append as env) a
                                           -> FuncTerm sem env ss r

data Dim (ss :: [Sig2 k]) where
  End  :: Dim '[]
  (:.) :: OfLength as -> Dim ss -> Dim ((as ':~> a) ': ss)

infixr 4 :.

fromFuncTerm :: FuncTerm sem env ss r
             -> Env (TermRep sem env) ss -> sem env r
fromFuncTerm f ENil              = f
fromFuncTerm f (ECons (TR x) xs) = fromFuncTerm (f x) xs

-- Corresponds to Env (URep sem) ss -> EnvI sem r
type family FuncU (sem :: [k] -> k -> Type) (ss :: [Sig2 k])
                  (r :: k) = res | res -> sem r where
  FuncU sem '[] r = EnvI sem r
  FuncU sem ((as ':~> a) ': ss) r = Func (EnvI sem) as (EnvI sem a)
                                    -> FuncU sem ss r

toFuncU :: Dim ss -> (Env (URep sem) ss -> EnvI sem r) -> FuncU sem ss r
toFuncU End f       = f ENil
toFuncU (n :. ns) f = \k -> toFuncU ns (f . ECons (toURep n k))

toURep :: OfLength as -> Func (EnvI sem) as (EnvI sem r) -> URep sem (as ':~> r)
toURep n f = UR (ofl2TEnv n) (fromFunc f)

ofl2TEnv :: OfLength as -> TEnv as
ofl2TEnv LZ     = ENil
ofl2TEnv (LS n) = ECons Proxy (ofl2TEnv n)

liftSOn :: forall sem ss r. LiftVariables sem => Dim ss
        -> (forall env. FuncTerm sem env ss r) -> FuncU sem ss r
liftSOn ns f =
  let h :: forall env. Env (TermRep sem env) ss -> sem env r
      h = fromFuncTerm f
  in toFuncU ns (liftSO @sem h)

