Embedding by Unembedding
========================

This is a proof-of-concept implementation of the idea presented in the paper: Kazutaka Matsuda, Samantha Frohlich, Meng Wang, and Nicolas Wu. 2023. Embedding by Unembedding. Proc. ACM Program. Lang. 7, ICFP, Article 189 (August 2023), 47 pages. <https://doi.org/10.1145/3607830>.

Some examples can be found in <https://github.com/kztk-m/EbU-examples>.

Overview
--------

Higher-order abstract syntax is one of the user-friendly ways to represent the EDSL's syntax.

```haskell
-- Finally-tagless style (Carette+ 09)
class MyLang e where 
  -- ... 
  add  :: e Int -> e Int -> e Int
  let_ :: e a -> (e a -> e b) -> e b 
```

However, since its expression type (constructor) in Haskell is parameterized by its guest type, it is unclear how can implement semantics that refers to environments (technically, semantics those that are defined for terms-in-context instead of closed terms).
Examples of such semantics include incremental computations, bidirectional transformations, and automatic differentiations.

This library provides operators that address this gap, based on [Atkey 09's unembedding](https://doi.org/10.1007/978-3-642-02273-9_5)---an provably correct isomorphism between de Bruijn-indexed terms and (parametric) higher-order abstract syntax.

```haskell
-- Assuming Sem is a semantic domain 
addSem :: Sem env Int -> Sem env Int -> Sem env Int 
letSem :: Sem env a -> Sem (a : env) b -> Sem env b 

instance MyLang (EnvI Sem) where 
  -- ...
  add = liftFO2 addSem -- or liftSO (ol0 :. ol0 :. End) addSem 
  let_ = liftSO (ol0 :. ol1 :. End) letSem
```