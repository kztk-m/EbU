Embedding by Unembedding
========================

This is a proof-of-concept implementation of [Embedding by Unembedding][EbU].

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

However, since the expression type operator (`e`) is parameterized only by its guest type, it is unclear how we can implement semantics that refers to environments (technically, semantics that are defined for terms-in-context instead of closed terms). 
Examples of such semantics include incremental computations, bidirectional transformations, and automatic differentiation.

This library provides operators that address this gap, based on [Atkey 09's unembedding](https://doi.org/10.1007/978-3-642-02273-9_5)---a provably correct isomorphism between de Bruijn-indexed terms and (parametric) higher-order abstract syntax.

```haskell
data Sem as a = ... -- semantic domain 

addSem :: Sem env Int -> Sem env Int -> Sem env Int 
letSem :: Sem env a -> Sem (a : env) b -> Sem env b 

instance MyLang (EnvI Sem) where 
  -- ...
  add = liftFO2 addSem -- or liftSO (ol0 :. ol0 :. End) addSem 
  let_ = liftSO (ol0 :. ol1 :. End) letSem
```

References
----------

* Kazutaka Matsuda, Samantha Frohlich, Meng Wang, and Nicolas Wu. 2023. [Embedding by Unembedding][EbU]. Proc. ACM Program. Lang. 7, ICFP, Article 189 (August 2023), 47 pages. 

[EBU]: https://doi.org/10.1145/3607830