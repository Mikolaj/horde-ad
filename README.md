# HORDE-AD: Higher Order Reverse Derivatives Efficiently

[![Hackage](https://img.shields.io/hackage/v/horde-ad.svg)](https://hackage.haskell.org/package/horde-ad)

Welcome to the Automatic Differentiation library originally inspired by the paper [_"Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"_](https://dl.acm.org/doi/10.1145/3498710). Compared to the paper and to classic taping AD Haskell packages, the library additionally efficiently supports array operations and generation of symbolic derivative programs, though the efficiency is confined to a narrowly typed class of source programs with limited higher-orderness. A detailed account of the extension is in the paper [_"Dual-Numbers Reverse AD for Functional Array Languages"_](http://arxiv.org/abs/2507.12640) by Tom Smeding, Mikolaj Konarski, Simon Peyton Jones and Andrew Fitzgibbon.
<!--
More specifically, in primitive pipelines (that match the Provable paper) the objective functions have types with ADVal in them which, e.g., permit dynamic control flow via inspecting the primal components of ADVal and permit higher order functions by just applying them (they are not symbolic for ADVal), but prevent vectorization, simplification and computing a derivative only once and evaluating on many inputs.
-->

This is an early prototype, both in terms of the engine performance, the API and the preliminary tools and examples built with it. At this development stage, it's not coded defensively but exactly the opposite: it will fail on cases not found in current tests so that new code and tests have to be added and old code optimized for the new specimens reported in the wild. The user should also be ready to add missing primitives and any obvious tools that should be predefined but aren't, such as weight normalization (https://github.com/Mikolaj/horde-ad/issues/42). It's already possible to differentiate basic neural network architectures, such as fully connected, recurrent, convolutional and residual. The library should also be suitable for defining exotic machine learning architectures and non-machine learning systems, given that no notion of a neural network nor of a computation graph are hardwired into the formalism, but instead they are compositionally and type-safely built up from general automatic differentiation building blocks.

Mature Haskell libraries with similar capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. See also https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md. Benchmarks suggest that horde-ad has competitive performance on CPU.
<!--
The benchmarks at _ (TBD after GHC 9.14 is out) show that this library has performance highly competitive with (i.e. faster than) those and PyTorch on CPU.
-->
It is hoped that the (well-typed) separation of AD logic and tensor manipulation backend will enable similar speedups on numerical accelerators, when their support is implemented. Contributions to this and other tasks are very welcome. The newcomer-friendly tickets are listed at https://github.com/Mikolaj/horde-ad/issues?q=is%3Aissue%20state%3Aopen%20label%3A%22good%20first%20issue%22. Please don't hesitate to ask questions on github, on Matrix, via email.


## Computing the derivative of a simple function

Here is an example of a Haskell function to be differentiated:
```hs
-- A function that goes from R^3 to R.
foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w  -- note that w appears twice
```

The gradient of `foo` instantiated to `Double` can be expressed in Haskell with horde-ad as:
```hs
gradFooDouble :: (Double, Double, Double) -> (Double, Double, Double)
gradFooDouble = fromDValue . cgrad foo . fromValue
```

which can be verified by computing the gradient at `(1.1, 2.2, 3.3)`:
```hs
>>> gradFooDouble (1.1, 2.2, 3.3)
(2.4396285219055063, -1.953374825727421, 0.9654825811012627)
```

We can instantiate `foo` to matrices (represented in the `Concrete` datatype of unboxed multi-dimensional arrays); the operations within (`sin`, `+`, `*`, etc.) applying elementwise:
```hs
type Matrix2x2 r = Concrete (TKS '[2, 2] r)  -- TKS means shapely-typed tensor kind
type ThreeMatrices r = (Matrix2x2 r, Matrix2x2 r, Matrix2x2 r)
threeSimpleMatrices :: ThreeMatrices Double
threeSimpleMatrices = (srepl 1.1, srepl 2.2, srepl 3.3)  -- srepl replicates its argument to fill the whole matrix
fooMatrixValue :: Matrix2x2 Double
fooMatrixValue = foo threeSimpleMatrices
>>> fooMatrixValue
sfromListLinear [2,2] [4.242393641025528,4.242393641025528,4.242393641025528,4.242393641025528])
```

Instantiated to matrices, `foo` now returns a matrix, not a scalar &mdash; but a gradient can only be computed of a function that returns a scalar.
To remediate this, let's sum the whole output of `foo` and only then compute its gradient: (note that `ssum0` returns a zero-dimensional array; `kfromS` extracts the (single) scalar from that)
```hs
gradSumFooMatrix :: ThreeMatrices Double -> ThreeMatrices Double
gradSumFooMatrix = cgrad (kfromS . ssum0 . foo)
```

This works as well as before:
```hs
>>> gradSumFooMatrix threeSimpleMatrices
(sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
```

### Efficiency: preserving sharing

We noted above that `w` appears twice in `foo`.  A property of tracing-based AD systems is that such re-use may not be captured, with explosive results.
In `cgrad`, such sharing is preserved, so `w` is processed only once during gradient computation and this property is guaranteed for the `cgrad` tool universally, without any action required from the user.
`horde-ad` also allows computing _symbolic_ derivative programs: with this API, a program is differentiated only once, after which it can be run on many different input values.
In this case, however, sharing is _not_ automatically preserved, so shared variables have to be explicitly marked using `tlet`, as shown below in `fooLet`.
This also makes the type of the function more specific: it now does not work on an arbitrary `Num` any more, but instead on an arbitrary `horde-ad` tensor that implements the standard arithmetic operations, some of which (e.g., `atan2H`) are implemented in custom numeric classes.
```hs
fooLet :: (RealFloatH (f r), ADReady f)  -- ADReady means the container type f supports AD
       => (f r, f r, f r) -> f r
fooLet (x, y, z) =
  tlet (x * sin y) $ \w ->
    atan2H z w + z * w  -- note that w still appears twice
```

### Vector-Jacobian product (VJP) and symbolic derivatives

The most general symbolic reverse derivative program for this function can be obtained using the `vjpArtifact` tool. Because the `vjp` family of tools permits non-scalar codomains (but expects an incoming cotangent argument to compensate, visible in the code below as `dret`), we illustrate it using the original `fooLet` from the previous section, without the need to add `ssum0`.
```hs
artifact :: AstArtifactRev (X (ThreeConcreteMatrices Double)) (TKS '[2, 2] Double)
artifact = vjpArtifact fooLet threeSimpleMatrices
```

The vector-Jacobian product program (presented below with additional formatting) looks like ordinary functional code with nested pairs and projections representing tuples. A quick inspection of the code reveals that computations are not repeated, which is thanks to the `tlet` used above.

```hs
>>> printArtifactPretty artifact
\dret m1 ->
  let m3 = sin (tproject2 (tproject1 m1))
      m4 = tproject1 (tproject1 m1) * m3
      m5 = recip (tproject2 m1 * tproject2 m1 + m4 * m4)
      m7 = (negate (tproject2 m1) * m5) * dret + tproject2 m1 * dret
  in tpair
       (tpair (m3 * m7)
              (cos (tproject2 (tproject1 m1)) * (tproject1 (tproject1 m1) * m7)))
       ((m4 * m5) * dret + m4 * dret)
```

A concrete value of this symbolic reverse derivative at the same input as before can be obtained by interpreting its program in the context of the operations supplied by the horde-ad library. (Note that the output happens to be the same as `gradSumFooMatrix threeSimpleMatrices` above, which used `cgrad` on `kfromS . ssum0 . foo`; the reason is that `srepl 1.0` happens to be the reverse derivative of `kfromS . ssum0`.)
```hs
>>> vjpInterpretArtifact artifact (toTarget threeSimpleMatrices) (srepl 1.0)
((sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627]) :: ThreeConcreteMatrices Double)
```

Note that, as evidenced by the `printArtifactPretty` call above, `artifact` contains the complete and simplified code of the VJP of `fooLet`, so repeated calls of `vjpInterpretArtifact artifact` won't ever repeat differentiation nor simplification and will only incur the cost of straightforward interpretation. The repeated call would fail with an error if the provided argument had a different shape than `threeSimpleMatrices`. However, for the examples we show here, such a scenario is ruled out by the types, because all tensors we present are shaped, meaning their full shape is stated in their type and so can't differ for two (tuples of) tensors of the same type. More loosely-typed variants of all the tensor operations, where runtime checks can really fail, are available in the horde-ad API and can be mixed and matched freely.

A shorthand that creates a symbolic gradient program, simplifies it and interprets it with a given input on the default CPU backend is called `grad` and is used exactly the same as (but with often much better performance on the same program than) `cgrad`:
```hs
>>> grad (kfromS . ssum0 . fooLet) threeSimpleMatrices
(sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
```


## For all shapes and sizes

An important feature of this library is a type system for tensor shape
arithmetic. The following code is part of a convolutional neural network
definition, for which horde-ad computes the shape of the gradient from
the shape of the input data and the initial parameters.
The Haskell compiler is able to infer many tensor shapes, deriving them both
from dynamic dimension arguments (the first two lines of parameters
to the function below) and from static type-level hints.

Let's look at the body of the `convMnistTwoS` function before we look at its signature. It is common to see neural network code like that, with shape annotations in comments, hidden from the compiler:
```hs
convMnistTwoS
  kh@SNat kw@SNat h@SNat w@SNat
  c_out@SNat _n_hidden@SNat batch_size@SNat
    -- integer parameters denoting basic dimensions
  input              -- input images, shape [batch_size, 1, h, w]
  (ker1, bias1)      -- layer1 kernel, shape [c_out, 1, kh+1, kw+1]; and bias, shape [c_out]
  (ker2, bias2)      -- layer2 kernel, shape [c_out, c_out, kh+1, kw+1]; and bias, shape [c_out]
  ( weightsDense     -- dense layer weights, shape [n_hidden, c_out * (h/4) * (w/4)]
  , biasesDense )    -- dense layer biases, shape [n_hidden]
  ( weightsReadout   -- readout layer weights, shape [10, n_hidden]
  , biasesReadout )  -- readout layer biases, shape [10]
  =                  -- -> output classification, shape [10, batch_size]
  assumeEquality @(Div (Div w 2) 2) @(Div w 4) $
  assumeEquality @(Div (Div h 2) 2) @(Div h 4) $
  let t1 = convMnistLayerS kh kw h w
                           (SNat @1) c_out batch_size
                           ker1 (sfromPrimal input) bias1
      t2 = convMnistLayerS kh kw (SNat @(h `Div` 2)) (SNat @(w `Div` 2))
                           c_out c_out batch_size
                           ker2 t1 bias2
      m1 = sreshape t2
      denseLayer = weightsDense `smatmul2` str m1
                   + str (sreplicate biasesDense)
  in weightsReadout `smatmul2` reluS denseLayer
     + str (sreplicate biasesReadout)
```
But we don't just want the shapes in comments and in runtime expressions; we want them as a compiler-verified documentation in the form of the type signature of the function:
```hs
convMnistTwoS
  :: forall kh kw h w c_out n_hidden batch_size target r.
     ( 1 <= kh  -- kernel height is large enough
     , 1 <= kw  -- kernel width is large enough
     , ADReady target, GoodScalar r, Differentiable r )
         -- GoodScalar means r is supported as array elements by horde-ad
  => SNat kh -> SNat kw -> SNat h -> SNat w
  -> SNat c_out -> SNat n_hidden -> SNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- SNat value parameters denoting basic dimensions
  -> PrimalOf target (TKS '[batch_size, 1, h, w] r)  -- `input` shape [batch_size, 1, h, w]
  -> ( ( target (TKS '[c_out, 1, kh + 1, kw + 1] r)  -- `ker1` shape [c_out, 1, kh+1, kw+1]
       , target (TKS '[c_out] r) )                   -- `bias2` shape [c_out]
     , ( target (TKS '[c_out, c_out, kh + 1, kw + 1] r)  -- `ker2` shape [c_out, c_out, kh+1, kw+1]
       , target (TKS '[c_out] r) )                       -- `bias2` shape [c_out]
     , ( target (TKS '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ] r)
           -- `weightsDense` shape [n_hidden, c_out * (h/4) * (w/4)]
       , target (TKS '[n_hidden] r) )    -- `biasesDense` shape [n_hidden]
     , ( target (TKS '[10, n_hidden] r)  -- `weightsReadout` shape [10, n_hidden]
       , target (TKS '[10] r) ) )        -- `biasesReadout` shape [10]
  -> target (TKS '[SizeMnistLabel, batch_size] r)  -- -> `output` shape [10, batch_size]
convMnistTwoS
  kh@SNat kw@SNat h@SNat w@SNat
  c_out@SNat _n_hidden@SNat batch_size@SNat
  input  -- input images
  (ker1, bias1)  -- layer1 kernel
  (ker2, bias2)  -- layer2 kernel
  ( weightsDense  -- dense layer weights
  , biasesDense )  -- dense layer biases
  ( weightsReadout  -- readout layer weights
  , biasesReadout )  -- readout layer biases
  =
...
```

This style gets verbose and the Haskell compiler needs some convincing to accept such programs, but type-safety is the reward. In practice, at least the parameters of the objective function are best expressed with shaped tensors, while the implementation can (zero-cost) convert the tensors to loosely typed variants as needed.

The full neural network definition from which this function is taken can be found at

https://github.com/Mikolaj/horde-ad/tree/master/example

in file `MnistCnnShaped2.hs` and the directory contains several other sample neural networks for MNIST digit classification. Among them are recurrent, convolutional and fully connected networks based on fully typed tensors (sizes of all dimensions are tracked in the types, as above) as well as on the weakly typed ranked tensors, where only tensor ranks are tracked. It's possible to mix the two typing styles within one function signature and even within one shape description.


Compilation from source
-----------------------

Horde-ad uses [ox-arrays](https://hackage.haskell.org/package/ox-arrays)
as its CPU backend library, which in turn is inspired by and depends
on [orthotope](https://hackage.haskell.org/package/orthotope).
Neither of these packages require any special installation.
Some of the other
[Haskell packages we depend on](https://github.com/Mikolaj/horde-ad/blob/master/horde-ad.cabal)
need their usual C library dependencies to be installed manually,
e.g., package zlib needs the C library zlib1g-dev or an equivalent.
At this time, we don't depend on any GPU hardware nor bindings.

For development, copying the included `cabal.project.local.development`
to `cabal.project.local` provides a sensible default to run `cabal build` with
and get compilation results relatively fast. For extensive testing,
on the other hand, a command like

    cabal test minimalTest --enable-optimization

ensures that the code is compiled with optimization and consequently
executes the rather computation-intensive testsuites in reasonable time.


Running tests
-------------

The `parallelTest` test suite consists of large tests and runs in parallel

    cabal test parallelTest --enable-optimization

which is likely to cause the extra printf messages coming from within
the tests to be out of order. To keep your screen tidy, simply redirect
`stderr`, e.g.,

    cabal test parallelTest --enable-optimization 2>/dev/null

The remainder of the test suite is set up to run sequentially, in part
to simplify automatic checking of results that may vary slightly
depending on execution order

    cabal test CAFlessTest --enable-optimization

The tests in this suite also don't contribute big Haskell CAFs,
which makes them more reliable micro-benchmarks. Ordinary
benchmarks that use package criterion are even more trustworthy,
but they don't have a comparable coverage at this time.


Coding style
------------

Stylish Haskell is used for slight auto-formatting at buffer save; see
[.stylish-haskell.yaml](https://github.com/Mikolaj/horde-ad/blob/master/.stylish-haskell.yaml).
As defined in the file, indentation is 2 spaces wide and screen is
80-columns wide. Spaces are used, not tabs. Spurious whitespace avoided.
Spaces around arithmetic operators encouraged.
Generally, relax and try to stick to the style apparent in a file
you are editing. Put big formatting changes in separate commits.

Haddocks should be provided for all module headers and for the main
functions and types from the most important modules.
Apart of that, only particularly significant functions and types
are distinguished by having a haddock. If minor ones have comments,
they should not be haddocks and they are permitted to describe
implementation details and be out of date. Prefer assertions in place
of comments, unless too verbose.


Copyright
---------

Copyright 2023--2025 Mikolaj Konarski, Well-Typed LLP and others (see git history)

License: BSD-3-Clause (see file LICENSE)
