# HORDE-AD: Higher Order Reverse Derivatives Efficiently

This is an Automatic Differentiation library based on the paper [_"Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"_](https://dl.acm.org/doi/10.1145/3498710) by Krawiec, Krishnaswami, Peyton Jones, Ellis, Fitzgibbon, and Eisenberg, developed in collaboration with the paper's authors. Compared to the paper, the library additionally efficiently supports array operations and generation of symbolic derivative programs, though the efficiency is confined to a narrowly typed class of source programs with limited higher-orderness.

This is an early prototype, both in terms of the engine performance, the API and the preliminary tools and examples built with it. The user should be ready to add missing primitives, as well as any obvious tools that should be predefined but aren't. It's already possible to differentiate basic neural network architectures, such as fully connected, recurrent, convolutional and residual. The library should also be suitable for defining exotic machine learning architectures and non-machine learning systems, given that the notion of a neural network is not hardwired into the formalism, but instead it's compositionally and type-safely built up from general automatic differentiation building blocks.

Mature Haskell libraries with similar capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. See also https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md. Benchmarks suggest that horde-ad has competitive performance on CPU. (TODO)
<!--
The benchmarks at SOMEWHERE show that this library has performance highly competitive with (i.e. faster than) those and PyTorch on CPU.
-->
It is hoped that the (well-typed) separation of AD logic and the tensor manipulation backend will enable similar speedups on numerical accelerators.


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

When `foo` is instantiated to matrices, which is a similarly trivial example as before due to the arithmetic operations working on the arrays element-wise, the gradient is:
```hs
type Matrix2x2 f r = f (TKS '[2, 2] r)
type ThreeMatrices r = (Matrix2x2 Concrete r, Matrix2x2 Concrete r, Matrix2x2 Concrete r)
threeSimpleMatrices :: ThreeMatrices Double
threeSimpleMatrices = (srepl 1.1, srepl 2.2, srepl 3.3)
gradFooMatrix :: (Differentiable r, GoodScalar r)
              => ThreeMatrices r -> ThreeMatrices r
gradFooMatrix = cgrad (kfromS . ssum0 . foo)
```

where we had to augment function `foo`, because `cgrad` expects a function with a scalar codomain (e.g., a loss function for neural networks). This works as well as before:
```hs
>>> gradFooMatrix threeSimpleMatrices
(sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
```

Note that `w` is processed only once during gradient computation and this property of sharing preservation is guaranteed for the `cgrad` tool universally, without any action required from the user. When computing symbolic derivative programs, however, the user has to explicitly mark values for sharing using `tlet` with a more specific type of the objective function, as shown below.

```hs
fooLet :: (RealFloatH (f r), LetTensor f)
       => (f r, f r, f r) -> f r
fooLet (x, y, z) =
  tlet (x * sin y) $ \w ->
    atan2H z w + z * w  -- note that w still appears twice
```

The most general symbolic gradient program for this function can be obtained using the `vjpArtifact` tool. We are using `fooLet` without `ssum0` this time, because the `vjp` family of tools by convention permits non-scalar codomains (but expects an incoming cotangent argument to compensate, visible in the code below as `dret`).
```hs
artifact :: AstArtifactRev (X (ThreeConcreteMatrices Double)) (TKS '[2, 2] Double)
artifact = vjpArtifact fooLet threeSimpleMatrices
```

The gradient program presented below with additional formatting looks like ordinary functional code with a lot of nested pairs and projections that represent tuples. A quick inspection of the gradient code reveals that computations are not repeated, which is thanks to the sharing mechanism, as promised above.

```hs
>>> printArtifactPretty artifact
"\dret m1 ->
   let m3 = sin (tproject2 (tproject1 m1))
       m4 = tproject1 (tproject1 m1) * m3
       m5 = recip (tproject2 m1 * tproject2 m1 + m4 * m4)
       m7 = (negate (tproject2 m1) * m5) * dret + tproject2 m1 * dret
    in tpair
         (tpair (m3 * m7)
                (cos (tproject2 (tproject1 m1)) * (tproject1 (tproject1 m1) * m7)))
         ((m4 * m5) * dret + m4 * dret)"
```

A concrete value of the symbolic gradient at the same input as before can be obtained by interpreting the gradient program in the context of the operations supplied by the horde-ad library. The value is the same as it would be for augmented `fooLet` evaluated by `cgrad` on the same input, as long as the incoming cotangent supplied for the interpretation consists of ones in all array cells, which is denoted by `srepl 1` in this case:

```hs
>>> vjpInterpretArtifact artifact (toTarget threeSimpleMatrices) (srepl 1)
((sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627]) :: ThreeConcreteMatrices Double)
```

A shorthand that creates the symbolic derivative program, simplifies it and interprets it with a given input on the default CPU backend is called `grad` and is used exactly the same as (but with often much better performance than) `cgrad`:
```hs
>>> grad (kfromS . ssum0 . fooLet) threeSimpleMatrices
(sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
```


## For all shapes and sizes

An additional feature of this library is a type system for tensor shape arithmetic. The following code is a part of convolutional neural network definition, for which horde-ad computes the gradient of a shape determined by the shape of input data and of initial parameters. The compiler is able to infer a lot of tensor shapes, deriving them both from dynamic dimension arguments (the first two lines of parameters to the function) and from static type-level hints. Look at this beauty.
```hs
convMnistTwoS
  kh@SNat kw@SNat h@SNat w@SNat
  c_out@SNat _n_hidden@SNat batch_size@SNat
    -- integer parameters denoting basic dimensions
  input              -- input images, shape [batch_size, 1, h, w]
  (ker1, bias1)      -- layer1 kernel, shape [c_out, 1, kh+1, kw+1]; and bias, shape [c_out]
  (ker2, bias2)      -- layer2 kernel, shape [c_out, c_out, kh+1, kw+1]; and bias, shape [c_out]
  ( weightsDense     -- dense layer weights,
                     -- shape [n_hidden, c_out * (h/4) * (w/4)]
  , biasesDense )    -- dense layer biases, shape [n_hidden]
  ( weightsReadout   -- readout layer weights, shape [10, n_hidden]
  , biasesReadout )  -- readout layer biases [10]
  =                  -- -> output classification, shape [10, batch_size]
  gcastWith (unsafeCoerceRefl :: Div (Div w 2) 2 :~: Div w 4) $
  gcastWith (unsafeCoerceRefl :: Div (Div h 2) 2 :~: Div h 4) $
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
  => SNat kh -> SNat kw -> SNat h -> SNat w
  -> SNat c_out -> SNat n_hidden -> SNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- SNat value parameters denoting basic dimensions
  -> PrimalOf target (TKS '[batch_size, 1, h, w] r)
  -> ( ( target (TKS '[c_out, 1, kh + 1, kw + 1] r)
       , target (TKS '[c_out] r) )
     , ( target (TKS '[c_out, c_out, kh + 1, kw + 1] r)
       , target (TKS '[c_out] r) )
     , ( target (TKS '[n_hidden, c_out * (h `Div` 4) * (w `Div` 4) ] r)
       , target (TKS '[n_hidden] r) )
     , ( target (TKS '[10, n_hidden] r)
       , target (TKS '[10] r) ) )
  -> target (TKS '[SizeMnistLabel, batch_size] r)
```

The full neural network definition from which this function is taken can be found at

https://github.com/Mikolaj/horde-ad/tree/master/example

in file `MnistCnnShaped2.hs` and the directory contains several other sample neural networks for MNIST digit classification. Among them are recurrent, convolutional and fully connected networks based on fully typed tensors (sizes of all dimensions are tracked in the types, as above) as well as their weakly typed variants that track only the ranks of tensors. It's possible to mix the two typing styles within one function signature and even within one shape description.


Compilation from source
-----------------------

The Haskell packages [we depend on](https://github.com/Mikolaj/horde-ad/blob/master/horde-ad.cabal) need their usual C library dependencies,
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

The remainder of the test suite is set up to run sequentially to simplify
automatic checking of results that may vary slightly depending on
execution order

    cabal test CAFlessTest --enable-optimization


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
implementation details and be out of date. Prefer assertions instead
of comments, unless too verbose.


Copyright
---------

Copyright 2023--2025 Mikolaj Konarski, Well-Typed LLP and others (see git history)

License: BSD-3-Clause (see file LICENSE)
