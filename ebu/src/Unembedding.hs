{- |

Contains unembedding framework to support using the Embedding by Unembedding technique.

-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Unembedding
  (
    -- * Interface Typeclass
    LiftVariables(..), Weakenable(..), Variables (..),

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
    liftFOF,

    -- * Lifting functions for second-order language constructs
    OfLength(..), LiftOfLength(..), ol0, ol1, ol2, ol3, ol4,
    FuncTerm, FuncU, Dim, DimSimple(..),
    liftSOn,

    -- ** Internal datatypes and functions used in 'liftSOn'.
    --
    -- | They are supposed to be used typically when a construct is variadic.

    Sig2(..), TermRep(..), URep(..),
    liftSO,

    -- * Lifting functions for languages with multiple semantic domains (experimental)
    liftFO0', liftFO1', liftFO2',
    liftFOF',

    liftFO', SemRepFO(..), HRepFO(..), SemSigFO(..),

    FuncSem', FuncH', Dim', DimMult(..), liftSOn',

    -- ** Interpretation functions
    runOpen', runOpenN', runClose',

    -- ** Internal datatypes underlying 'liftSOn''

    SemSig(..), SemRep'(..), HRep'(..), liftSO',
    liftSOF',

    -- * More generalized interface for nested EbU
    FuncSemGen, FuncHGen, DimNested(..), BDesc(..), DimGen,
    liftSOnGen, liftSOGen,
    BsFunc, BsFuncSem,

    -- ** Internal datatypes and functions used in 'liftSOnGen'

    KBindSpec(..), BindSpec(..), ArgSpec(..),
    HRepK(..), HRepGen(..), SemRepK(..), SemRepGen(..),

    -- * Internal Manipulation of Variables
    var0, var1, var2,

  ) where

import           Data.Kind       (Type)
import           Data.Proxy      (Proxy (..))
import           Unsafe.Coerce   (unsafeCoerce)

import           Unembedding.Env

-- | Value-level representation of guest's typing environments.
type TEnv     = Env Proxy

-- | Weakenable semantics.
class Weakenable (sem :: [k] -> k' -> Type) where
  weaken :: sem as a -> sem (b : as) a

  -- | Generic weakening
  --   Compares two environments and repeatedly applies 'weaken' to unify them
  --   While it appears partial, it is guaranteed to work by the original unembedding work.
  -- weaken + compare
  weakenMany :: TEnv as -> TEnv as' -> sem as b -> sem as' b
  weakenMany e1 e2 = go lenDiff e1 e2
    where
      l1 = lenEnv e1
      l2 = lenEnv e2
      lenDiff = l2 - l1 -- must be positive
      go :: forall as as' b. Int -> TEnv as -> TEnv as' -> sem as b -> sem as' b
      go 0 _   _             ls = unsafeCoerce ls
      go n e1' (ECons _ e2') ls = weaken $ go (n-1) e1' e2' ls
      go _ _    _            _  = error $ "weakenMany: the first argument (len: " ++ show l1 ++  ") is smaller than the second (lens: " ++ show l2 ++ ")"

-- | Defines semantics that can be unembed: those that have an environment that can
--   focus on a variable, and be weakened

class Weakenable semvar => Variables (semvar :: [k] -> k -> Type) where
  var    :: semvar (a ': as) a

instance Weakenable Ix where
  weaken = IxS

-- | Ix is a free instance of 'Variables'.
instance Variables Ix where
  var = IxZ


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
  type family Var sem :: [k] -> k -> Type
  type Var sem = sem

  liftVar :: Var sem env a -> sem env a
  default liftVar :: (Var sem ~ sem) => Var sem env a -> sem env a
  liftVar = id

instance LiftVariables Ix where

-- | Wrapper the quantifies over env so that our type can only have one param like the HOAS
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
runOpen = runOpen'

-- | Same vibe as runOpen just with N free variables, represented as type env
runOpenN :: LiftVariables sem => TEnv as -> (Env (EnvI sem) as -> EnvI sem a) -> sem as a
runOpenN = runOpenN'

-- | A special case of 'runOpenN'
runClose :: EnvI sem a -> sem '[] a
runClose e = runEnvI e ENil

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

liftFOF :: (forall env. (forall a. key a -> sem env a) -> sem env r) -> (forall a. key a -> EnvI sem a) -> EnvI sem r
liftFOF f a = EnvI $ \sh -> f (\key -> runEnvI (a key) sh)

-- when it comes to second order constructors, now the arguments can have arguments
-- and we need to accommodate for that
-- the following are ways of describing those arguments:

-- | describes arguments of second order constructs. Intended to appear at the type level
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
        conv e (UR e1 k) = TR $ convertConstructArg e e1 k

-- Here down is the type families (leave in appendix)

data OfLength as where
  LZ :: OfLength '[]
  LS :: !(OfLength as) -> OfLength (a ': as)

-- | Class to reuse 'ol1', ..., 'ol4' for 'liftSOn', 'liftSOn'', and 'liftSOnGen'.
class LiftOfLength f as t | t -> as where
  liftOfLength :: OfLength as -> f t

instance LiftOfLength OfLength as as where
  liftOfLength = id



-- handy short cuts for values:

-- | Smart constructor for an 'OfLength' zero.
ol0 :: LiftOfLength f '[] t => f t
ol0 = liftOfLength LZ

-- | Smart constructor for an 'OfLength' one.
ol1 :: LiftOfLength f '[a] t => f t
ol1 = liftOfLength $ LS LZ

-- | Smart constructor for an 'OfLength' two.
ol2 :: LiftOfLength f '[a,b] t => f t
ol2 = liftOfLength $ LS ol1

-- | Smart constructor for an 'OfLength' three.
ol3 :: LiftOfLength f '[a,b,c] t => f t
ol3 = liftOfLength $ LS ol2

-- | Smart constructor for an 'OfLength' four.
ol4 :: LiftOfLength f '[a,b,c,d] t => f t
ol4 = liftOfLength $ LS ol3

-- Corresponds to (forall env. Env (TermRep sem env) ss -> sem env r)
type family FuncTerm (sem :: [k] -> k -> Type) (env :: [k])
                     (ss :: [Sig2 k]) (r :: k) | r -> sem env r where
  FuncTerm sem env '[] r = sem env r
  FuncTerm sem env ((as ':~> a) ': ss) r = sem (Append as env) a
                                           -> FuncTerm sem env ss r

-- data Dim (ss :: [Sig2 k]) where
--   End  :: Dim '[]
--   (:.) :: OfLength as -> Dim ss -> Dim ((as ':~> a) ': ss)
-- infixr 4 :.

data DimSimple (s :: Sig2 k) where
  DimSimple :: !(OfLength as) -> DimSimple (as ':~> a)

instance t ~ (as ':~> a) => LiftOfLength DimSimple as t where
  liftOfLength = DimSimple



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
toFuncU ENil f                     = f ENil
toFuncU (ECons (DimSimple n) ns) f = \k -> toFuncU ns (f . ECons (toURep n k))

toURep :: OfLength as -> Func (EnvI sem) as (EnvI sem r) -> URep sem (as ':~> r)
toURep n f = UR (ofl2TEnv n) (fromFunc f)

ofl2TEnv :: OfLength as -> TEnv as
ofl2TEnv LZ     = ENil
ofl2TEnv (LS n) = ECons Proxy (ofl2TEnv n)

type Dim = Env DimSimple


-- | Handy version of 'liftSO'. The type looks complicated but can be comprehensive
-- when we apply it to specific @Dim ss@ values.
--
-- >>> :t liftSOn (ol0 :. ol0 :. ENil)
-- >>> :t liftSOn (ol1 :. ENil)
-- >>> :t liftSOn (ol0 :. ol2 :. ENil)
-- liftSOn (ol0 :. ol0 :. ENil)
--   :: forall {k2} {sem :: [k2] -> k2 -> *} {a1 :: k2} {a2 :: k2}
--             {r :: k2}.
--      LiftVariables sem =>
--      (forall (env :: [k2]). sem env a1 -> sem env a2 -> sem env r)
--      -> EnvI sem a1 -> EnvI sem a2 -> EnvI sem r
-- liftSOn (ol1 :. ENil)
--   :: forall {k2} {sem :: [k2] -> k2 -> *} {a1 :: k2} {a2 :: k2}
--             {r :: k2}.
--      LiftVariables sem =>
--      (forall (env :: [k2]). sem (a1 : env) a2 -> sem env r)
--      -> (EnvI sem a1 -> EnvI sem a2) -> EnvI sem r
-- liftSOn (ol0 :. ol2 :. ENil)
--   :: forall {k2} {sem :: [k2] -> k2 -> *} {a1 :: k2} {a2 :: k2}
--             {b :: k2} {a3 :: k2} {r :: k2}.
--      LiftVariables sem =>
--      (forall (env :: [k2]).
--       sem env a1 -> sem (a2 : b : env) a3 -> sem env r)
--      -> EnvI sem a1
--      -> (EnvI sem a2 -> EnvI sem b -> EnvI sem a3)
--      -> EnvI sem r
liftSOn :: forall sem ss r. LiftVariables sem => Dim ss
        -> (forall env. FuncTerm sem env ss r) -> FuncU sem ss r
liftSOn ns f =
  let h :: forall env. Env (TermRep sem env) ss -> sem env r
      h = fromFuncTerm f
  in toFuncU ns (liftSO @sem h)

{-
Multi-sorted I/F for supporting languages with more than one syntactic category.

This connect

   sem1 (as1 ++ env) a1 -> sem2 (as2 ++ env) a2 -> ... -> semn (asn ++ env) an -> sem env a

with

   (Env exp as1 -> h1 a1) -> (Env exp as2 -> h2 a2) -> ... -> (Env exp asn -> hn an) -> hn a

Notice the use of exp in HOAS representations.

-}

data SemSig k = forall k'. MkSemSig ([k] -> k' -> Type) [k] k'

-- "semantic domain" representation.
data SemRep' (env :: [k]) (semsig :: SemSig k) where
  SemR' :: sem (Append as env) b -> SemRep' env (MkSemSig sem as b)

-- HOAS representation.
data HRep' (semExp :: [k] -> k -> Type) (s :: SemSig k) where
  HR' :: TEnv as -> (Env (EnvI semExp) as -> EnvI sem b) -> HRep' semExp (MkSemSig sem as b)

convertConstructArg :: LiftVariables semExp => TEnv env -> TEnv as -> (Env (EnvI semExp) as -> EnvI sem b) -> sem (Append as env) b
convertConstructArg shEnv shAs k =
  let shAsEnv = appendEnv shAs shEnv        -- TEnv (as ++ env)
      xs = makeVariables shEnv shAs shAsEnv -- Env (EnvI semExp) as
  in runEnvI (k xs) shAsEnv

makeVariables :: LiftVariables semExp => proxy env -> TEnv as -> TEnv (Append as env) -> Env (EnvI semExp) as
makeVariables _ ENil _ = ENil
makeVariables p (ECons _ shAs) te@(ECons _ te') =
      let x = EnvI $ \e' -> liftVar $ weakenMany te e' var
      in ECons x (makeVariables p shAs te')

convertHRep'toSemRep' :: LiftVariables semE => TEnv env -> HRep' semE x -> SemRep' env x
convertHRep'toSemRep' shEnv (HR' shAs k) = SemR' $ convertConstructArg shEnv shAs k

-- | Core function to lift second-order constructs, supporting multiple semantic domains.
liftSO' :: forall semExp sem ss r. LiftVariables semExp =>
  (forall env. Env (SemRep' env) ss -> sem env r)
  -> Env (HRep' semExp) ss -> EnvI sem r
liftSO' f ks = EnvI $ \shEnv -> f (mapEnv (convertHRep'toSemRep' shEnv) ks)

-- | A general form of 'liftSO'' where constructs to be lifted allowed to have
-- infinitely many arguments. 'liftSO'' is a special case where `h = Ix ss`.
liftSOF' :: forall semE sem h r. LiftVariables semE =>
  (forall env. (forall semsig. h semsig -> SemRep' env semsig) -> sem env r)
  -> (forall semsig. h semsig -> HRep' semE semsig) -> EnvI sem r
liftSOF' f k = EnvI $ \shEnv -> f (convertHRep'toSemRep' shEnv . k)

toHRep' :: OfLength as -> Func (EnvI semExp) as (EnvI sem r) -> HRep' semExp (MkSemSig sem as r)
toHRep' n f = HR' (ofl2TEnv n) (fromFunc f)


-- -- Corresponds to Env (HRep' semExp) ss -> EnvI semR r
type family FuncH' (semExp :: [k] -> k -> Type) (semR :: [k] -> kR -> Type) (ss :: [SemSig k])
                   (r :: kR) = res | res -> semR r k where
  FuncH' semExp semR '[] r = EnvI semR r
  FuncH' semExp semR (MkSemSig sem as a ': ss) r =
    Func (EnvI semExp) as (EnvI sem a)
    -> FuncH' semExp semR ss r

toFuncH' :: Dim' ss -> (Env (HRep' semExp) ss -> EnvI semR r) -> FuncH' semExp semR ss r
toFuncH' ENil f              = f ENil
toFuncH' (DimMult n :. ns) f = \k -> toFuncH' ns (f . ECons (toHRep' n k))

-- data Dim' (ss :: [SemSig k]) where
--   End'  :: Dim' '[]
--   (::.) :: OfLength as -> Dim' ss -> Dim' (MkSemSig sem as a ': ss)

-- infixr 4 ::.

data DimMult (s :: SemSig k) where
  DimMult :: !(OfLength as) -> DimMult (MkSemSig sem as a)

instance t ~ MkSemSig sem as a => LiftOfLength DimMult as t where
  liftOfLength = DimMult

type Dim' = Env DimMult


-- Corresponds to (forall env. Env (SemRep' env) ss -> semR env r)
type family FuncSem' (semR :: [k] -> kR -> Type) (env :: [k])
                     (ss :: [SemSig k]) (r :: kR) | r -> semR env r where
  FuncSem' semR env '[] r = semR env r
  FuncSem' semR env (MkSemSig sem as a ': ss) r = sem (Append as env) a -> FuncSem' semR env ss r

fromFuncSem' :: FuncSem' semR env ss r -> Env (SemRep' env) ss -> semR env r
fromFuncSem' f ENil                 = f
fromFuncSem' f (ECons (SemR' x) xs) = fromFuncSem' (f x) xs

-- | Handy version of 'liftSO'. Unlike 'liftSOn', it requires @proxy semExp@ to determine which
-- semantic domain variables are in.
--
-- >>> :t liftSOn' ENil (Proxy @Ix)
-- liftSOn' ENil (Proxy @Ix)
--   :: forall {k} {kR} {semR :: [k] -> kR -> *} {r :: kR}.
--      (forall (env :: [k]). semR env r) -> EnvI semR r
-- >>> :t liftSOn' (ol0 :. ol0 :. ENil)
-- >>> :t liftSOn' (ol1 :. ENil)
-- liftSOn' (ol0 :. ol0 :. ENil)
--   :: forall {k2} {kR} {k'1} {k'2} {semExp :: [k2] -> k2 -> *}
--             {proxy :: ([k2] -> k2 -> *) -> *} {semR :: [k2] -> kR -> *}
--             {sem1 :: [k2] -> k'1 -> *} {a1 :: k'1} {sem2 :: [k2] -> k'2 -> *}
--             {a2 :: k'2} {r :: kR}.
--      LiftVariables semExp =>
--      proxy semExp
--      -> (forall (env :: [k2]). sem1 env a1 -> sem2 env a2 -> semR env r)
--      -> EnvI sem1 a1
--      -> EnvI sem2 a2
--      -> EnvI semR r
-- liftSOn' (ol1 :. ENil)
--   :: forall {k2} {kR} {k'} {semExp :: [k2] -> k2 -> *}
--             {proxy :: ([k2] -> k2 -> *) -> *} {semR :: [k2] -> kR -> *}
--             {sem :: [k2] -> k' -> *} {a1 :: k2} {a2 :: k'} {r :: kR}.
--      LiftVariables semExp =>
--      proxy semExp
--      -> (forall (env :: [k2]). sem (a1 : env) a2 -> semR env r)
--      -> (EnvI semExp a1 -> EnvI sem a2)
--      -> EnvI semR r
liftSOn' ::
  forall semExp semR ss r proxy.
  LiftVariables semExp =>
  Dim' ss
  -> proxy semExp
  -> (forall env. FuncSem' semR env ss r)
  -> FuncH' semExp semR ss r
liftSOn' ns _ f =
  let h :: forall env. Env (SemRep' env) ss -> semR env r
      h = fromFuncSem' f
  in toFuncH' ns (liftSO' @semExp h)









data SemSigFO k = forall k'. MkSemSigFO ([k] -> k' -> Type) k'


data SemRepFO (env :: [k]) (semsig :: SemSigFO k) where
  SemRFO :: sem env b -> SemRepFO env (MkSemSigFO sem b)

data HRepFO (s :: SemSigFO k) where
  HRFO :: EnvI sem b -> HRepFO (MkSemSigFO sem b)


liftFO' :: (forall env. Env (SemRepFO env) ss -> sem env a)
       -> Env HRepFO ss
       -> EnvI sem a
liftFO' f xs = EnvI $ \e -> f (mapEnv (\(HRFO (EnvI t)) -> SemRFO (t e)) xs)

liftFO0' :: (forall env. sem env a) -> EnvI sem a
liftFO0' = liftFO0

liftFO1' :: (forall env. sem1 env a -> sem2 env b) -> EnvI sem1 a -> EnvI sem2 b
liftFO1' f e = liftFO' (\(ECons (SemRFO x) _) -> f x)  (ECons (HRFO e) ENil)

liftFO2' :: (forall env. sem1 env a -> sem2 env b -> sem3 env c) -> EnvI sem1 a -> EnvI sem2 b -> EnvI sem3 c
liftFO2' f e1 e2 = liftFO' (\(ECons (SemRFO x) (ECons (SemRFO y) _)) -> f x y) (ECons (HRFO e1) (ECons (HRFO e2) ENil))

liftFOF' :: (forall env. (forall sem a. key sem a -> sem env a) -> semR env r) -> (forall sem a. key sem a -> EnvI sem a) -> EnvI semR r
liftFOF' f arg  = EnvI $ \sh -> f (\key -> runEnvI (arg key) sh)

runOpen' :: LiftVariables semE => (EnvI semE a -> EnvI sem b) -> sem '[a] b
runOpen' f = runOpenN' (ECons Proxy ENil) (\(ECons x _) -> f x)

-- | Same vibe as 'runOpen'' just with N free variables, represented as type env
runOpenN' :: LiftVariables semE => TEnv as -> (Env (EnvI semE) as -> EnvI sem a) -> sem as a
runOpenN' e f =
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

-- | A special case of 'runOpenN''
runClose' :: EnvI sem a -> sem '[] a
runClose' e = runEnvI e ENil

{-
Further generalized interface.
-}


-- | A pair of semantic domain and a type.
data KBindSpec k = forall k'. MkKBindSpec ([k] -> k' -> Type) k'

-- | Binder spec. @MkBindSpec [a1,...,an] [MkKBindSpec sem1 b1, ..., MkKBindSpec semm bm]@
-- express that a binder binds @[a1,...,an,b1,...,bm]@, in which
--    * @a1,...,an@ are to be unembedded
--    * @b1,...,bm@ are kept for the future processing (hence they are compled with semantic domains)
data BindSpec k = MkBindSpec [k] [KBindSpec k]

-- | A spec for a language construct argument.
data ArgSpec k =
  forall k'. MkArgSpec
    ([k] -> k' -> Type) -- ^ The semantic domain for the argument to be interpreted.
    (BindSpec k) -- ^ The binder spec of the argument
    k' -- ^ The (guest) type of the argument

-- | "semantic domain" represention for "k"ept bindings
data SemRepK (env :: [k]) (kbspec :: KBindSpec k) where
  SemRK :: Weakenable sem => sem env a -> SemRepK env (MkKBindSpec sem a)
-- | "semantic domain" representation.
data SemRepGen (env :: [k]) (aspec :: ArgSpec k) where
  SemRGen :: (Env (SemRepK (Append as env)) bs -> sem (Append as env) b) -> SemRepGen env (MkArgSpec sem (MkBindSpec as bs) b)

-- | HOAS represention for "k"ept bindings
data HRepK (kbspec :: KBindSpec k) where
  HRK :: EnvI sem a -> HRepK (MkKBindSpec sem a)

-- | HOAS representation.
data HRepGen (semExp :: [k] -> k -> Type) (aspec :: ArgSpec k) where
  HRGen :: TEnv as -> (Env (EnvI semExp) as -> Env HRepK bs -> EnvI sem b) -> HRepGen semExp (MkArgSpec sem (MkBindSpec as bs) b)

convertHtoSemGen :: LiftVariables semE => TEnv env -> HRepGen semE x -> SemRepGen env x
convertHtoSemGen shEnv (HRGen shAs k) = SemRGen $ convertConstructArgGen shEnv shAs k

convertConstructArgGen :: LiftVariables semE => TEnv env -> TEnv as -> (Env (EnvI semE) as -> Env HRepK bs -> EnvI sem b) -> Env (SemRepK (Append as env)) bs -> sem (Append as env) b
convertConstructArgGen shEnv shAs k kargs =
  let shAsEnv = appendEnv shAs shEnv        -- TEnv (Append as env)
      xs = makeVariables shEnv shAs shAsEnv -- Env (EnvI semExp) as
  in runEnvI (k xs (weakenAll shAsEnv kargs)) shAsEnv

weakenAll :: TEnv env' -> Env (SemRepK env') bs -> Env HRepK bs
weakenAll shAsEnv = mapEnv (\(SemRK s) -> HRK $ EnvI $ \tenv' -> weakenMany shAsEnv tenv' s)

-- | Core function to lift second-order constructs, supporting multiple semantic
-- domains and selective unembedding.
liftSOGen :: forall semExp sem ss r. LiftVariables semExp =>
  (forall env. Env (SemRepGen env) ss -> sem env r)
  -> Env (HRepGen semExp) ss -> EnvI sem r
liftSOGen f ks = EnvI $ \shEnv -> f (mapEnv (convertHtoSemGen shEnv) ks)

-- | Binding description.
data BDesc (as :: [k]) (bs :: [KBindSpec k]) where
  E :: BDesc '[] '[]
  -- | stands for the corresponding binding is to be kept (for further processing afterwards).
  K :: Weakenable sem => !(BDesc as bs) -> BDesc as (MkKBindSpec sem b : bs)
  -- | stands for the corresponding binding is to be unembedded.
  U :: !(BDesc as bs) -> BDesc (a : as) bs

descToTEnv :: BDesc as bs -> TEnv as
descToTEnv E     = ENil
descToTEnv (K d) = descToTEnv d
descToTEnv (U d) = ECons Proxy (descToTEnv d)

type family BsFunc (bs :: [KBindSpec k]) semR r = res | res -> semR r where
  BsFunc '[] semR r = EnvI semR r
  BsFunc (MkKBindSpec sem b : bs) semR r = EnvI sem b -> BsFunc bs semR r

fromBsFunc :: BDesc as bs -> BsFunc bs semR r -> Env HRepK bs -> EnvI semR r
fromBsFunc E f _                      = f
fromBsFunc (K d) f (ECons (HRK e) es) = fromBsFunc d (f e) es
fromBsFunc (U d) f es                 = fromBsFunc d f es


toHRepGen :: BDesc as bs -> Func (EnvI semExp) as (BsFunc bs semR r) -> HRepGen semExp (MkArgSpec semR (MkBindSpec as bs) r)
toHRepGen d f = HRGen (descToTEnv d) (fromBsFunc d . fromFunc f)

data DimNested (s :: ArgSpec k) where
  DimNested :: !(BDesc as bs) -> DimNested (MkArgSpec sem (MkBindSpec as bs) a)

instance t ~ MkArgSpec sem (MkBindSpec as '[]) a => LiftOfLength DimNested as t where
  liftOfLength = DimNested . go
    where
      go :: OfLength xs -> BDesc xs '[]
      go LZ     = E
      go (LS x) = U (go x)

type DimGen = Env DimNested

type family FuncHGen
      (semExp :: [k] -> k -> Type)
      (semR   :: [k] -> kR -> Type)
      (ss :: [ArgSpec k]) (r :: kR) = res | res -> semR r k where
  FuncHGen semExp semR '[] r = EnvI semR r
  FuncHGen semExp semR (MkArgSpec sem (MkBindSpec as bs) a : ss) r =
    Func (EnvI semExp) as (BsFunc bs sem a)
    -> FuncHGen semExp semR ss r

toFuncHGen :: DimGen ss -> (Env (HRepGen semExp) ss -> EnvI semR r) -> FuncHGen semExp semR ss r
toFuncHGen ENil f         = f ENil
toFuncHGen (ECons (DimNested d) ds) f = \k -> toFuncHGen ds (f . ECons (toHRepGen d k))


type family BsFuncSem (bs :: [KBindSpec k]) (env :: [k]) r = res where
  BsFuncSem '[] env r = r
  BsFuncSem (MkKBindSpec sem b : bs) env r = sem env b -> BsFuncSem bs env r

type family FuncSemGen
       (semR :: [k] -> kR -> Type)
       (env :: [k])
       (ss :: [ArgSpec k]) (r :: kR) | r -> semR env r where
  FuncSemGen semR env '[] r = semR env r
  FuncSemGen semR env (MkArgSpec sem (MkBindSpec as bs) a ': ss) r =
    BsFuncSem bs (Append as env) (sem (Append as env) a)
    -> FuncSemGen semR env ss r

fromFuncSemK ::
  BDesc as0 bs -> (Env (SemRepK asenv) bs -> sem asenv b) -> BsFuncSem bs asenv (sem asenv b)
fromFuncSemK E f     = f ENil
fromFuncSemK (U d) f = fromFuncSemK d f
fromFuncSemK (K d) f = \s -> fromFuncSemK d (f . ECons (SemRK s))

fromFuncSemGen :: DimGen ss -> FuncSemGen semR env ss r -> Env (SemRepGen env) ss -> semR env r
fromFuncSemGen _ f ENil = f
fromFuncSemGen (DimNested d :. ds) f (ECons (SemRGen x) xs) =
  fromFuncSemGen ds (f $ fromFuncSemK d x) xs

-- | Further generation of 'liftSOn''.
--
-- >>> :t liftSOnGen (DimNested (K E) :. ENil) Proxy
-- liftSOnGen (DimNested (K E) :. ENil) Proxy
--   :: forall {k} {k'1} {kR} {k'2} {semExp :: [k] -> k -> *}
--             {sem1 :: [k] -> k'1 -> *} {semR :: [k] -> kR -> *}
--             {sem2 :: [k] -> k'2 -> *} {b :: k'1} {a :: k'2} {r :: kR}.
--      (LiftVariables semExp, Weakenable sem1) =>
--      (forall (env :: [k]). (sem1 env b -> sem2 env a) -> semR env r)
--      -> (EnvI sem1 b -> EnvI sem2 a) -> EnvI semR r
-- >>> :t liftSOnGen (ol1 :. ENil) Proxy
-- liftSOnGen (ol1 :. ENil) Proxy
--   :: forall {k2} {kR} {k'} {semExp :: [k2] -> k2 -> *}
--             {semR :: [k2] -> kR -> *} {sem :: [k2] -> k' -> *} {a1 :: k2}
--             {a2 :: k'} {r :: kR}.
--      LiftVariables semExp =>
--      (forall (env :: [k2]). sem (a1 : env) a2 -> semR env r)
--      -> (EnvI semExp a1 -> EnvI sem a2) -> EnvI semR r
-- >>> :t liftSOnGen (DimNested (K (U E)) :. ENil) Proxy
-- liftSOnGen (DimNested (K (U E)) :. ENil) Proxy
--   :: forall {k} {k'1} {kR} {k'2} {semExp :: [k] -> k -> *}
--             {sem1 :: [k] -> k'1 -> *} {semR :: [k] -> kR -> *}
--             {sem2 :: [k] -> k'2 -> *} {a1 :: k} {b :: k'1} {a2 :: k'2}
--             {r :: kR}.
--      (LiftVariables semExp, Weakenable sem1) =>
--      (forall (env :: [k]).
--       (sem1 (a1 : env) b -> sem2 (a1 : env) a2) -> semR env r)
--      -> (EnvI semExp a1 -> EnvI sem1 b -> EnvI sem2 a2) -> EnvI semR r
-- >>> :t liftSOnGen (ol0 :. DimNested (K E) :. ENil) Proxy
-- liftSOnGen (ol0 :. DimNested (K E) :. ENil) Proxy
--   :: forall {k2} {k'1} {kR} {k'2} {k'3} {semExp :: [k2] -> k2 -> *}
--             {sem1 :: [k2] -> k'1 -> *} {semR :: [k2] -> kR -> *}
--             {sem2 :: [k2] -> k'2 -> *} {a1 :: k'2} {sem3 :: [k2] -> k'3 -> *}
--             {b :: k'1} {a2 :: k'3} {r :: kR}.
--      (LiftVariables semExp, Weakenable sem1) =>
--      (forall (env :: [k2]).
--       sem2 env a1 -> (sem1 env b -> sem3 env a2) -> semR env r)
--      -> EnvI sem2 a1 -> (EnvI sem1 b -> EnvI sem3 a2) -> EnvI semR r


liftSOnGen ::
  forall semExp semR ss r proxy.
  LiftVariables semExp =>
  DimGen ss
  -> proxy semExp
  -> (forall env. FuncSemGen semR env ss r)
  -> FuncHGen semExp semR ss r
liftSOnGen ds _ f =
 let h :: forall env. Env (SemRepGen env) ss -> semR env r
     h = fromFuncSemGen ds f
  in toFuncHGen ds (liftSOGen @semExp h)

