# HORDE-AD: Higher Order Reverse Derivatives Efficiently

This is an Automatic Differentiation library based on the paper [_"Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"_](https://dl.acm.org/doi/10.1145/3498710) by Krawiec, Krishnaswami, Peyton Jones, Ellis, Fitzgibbon, and Eisenberg, developed in collaboration with the paper's authors. Compared to the paper, the library additionally efficiently supports array operations and generation of symbolic derivative programs, though the efficiency is confined to a narrowly typed class of source programs with limited higher-orderness.

This is an early prototype, both in terms of the engine performance, the API and the preliminary tools and examples built with it. The user should be ready to add missing primitives, as well as any obvious tools that should be predefined but aren't. It's already possible to differentiate basic neural network architectures, such as fully connected, recurrent, convolutional and residual. The library should also be suitable for defining exotic machine learning architectures and non-machine learning systems, given that the notion of a neural network is not hardwired into the formalism, but instead it's compositionally and type-safely built up from general automatic differentiation building blocks.

Mature Haskell libraries with similar capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. See also https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md. Benchmarks suggest that horde-ad has competitive performance. (TODO: boasting)
<!--
-- TODO: do and redo the benchmarks

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
gradFooDouble = fromDValue . crev foo . fromValue
```

which can be verified by computing the gradient at `(1.1, 2.2, 3.3)`:
```hs
>>> gradFooDouble (1.1, 2.2, 3.3)
(2.4396285219055063, -1.953374825727421, 0.9654825811012627)
```

Instantiated to matrices, the gradient is:
```hs
type TwoByTwoMatrix f r = f (TKS '[2, 2] r)
type ThreeConcreteMatrices r = (TwoByTwoMatrix RepN r, TwoByTwoMatrix RepN r, TwoByTwoMatrix RepN r)
threeSimpleMatrices :: ThreeConcreteMatrices Double
threeSimpleMatrices = (srepl 1.1, srepl 2.2, srepl 3.3)
gradFooMatrix :: (Differentiable r, GoodScalar r)
              => ThreeConcreteMatrices r -> ThreeConcreteMatrices r
gradFooMatrix = crev foo
```

as can be verified by:
```hs
>>> gradFooMatrix threeSimpleMatrices
(sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
```

Note that `w` is processed only once during gradient computation and this property of sharing preservation is guaranteed for the `crev` tool universally, without any action required from the user. When computing symbolic derivative programs, however, the user has to explicitly mark values for sharing using `tlet` with a more specific type of the objective function, as shown below.

```hs
fooLet :: (RealFloatH (f r), LetTensor f)
       => (f r, f r, f r) -> f r
fooLet (x, y, z) =
  tlet (x * sin y) $ \w ->
    atan2H z w + z * w
```

The symbolic gradient program (here presented with additional formatting) can be then obtained using the `revArtifactAdapt` tool:
```hs
>>> printArtifactPretty
      (let staticShapes = tftk @RepN knownSTK (toTarget threeSimpleMatrices)
       in fst $ revArtifactAdapt True fooLet staticShapes)
"\dret m1 ->
   let m3 = sin (tproject2 (tproject1 m1))
       m4 = tproject1 (tproject1 m1) * m3
       m5 = recip (tproject2 m1 * tproject2 m1 + m4 * m4)
       m7 = (negate (tproject2 m1) * m5) * dret + tproject2 m1 * dret
    in tpair
         ( tpair (m3 * m7, cos (tproject2 (tproject1 m1)) * (tproject1 (tproject1 m1) * m7))
         , (m4 * m5) * dret + m4 * dret)
```

A quick inspection of the gradient program reveals that computations are not repeated, which is thanks to the sharing mechanism. A concrete value of the symbolic gradient at the same input as before can be obtained by interpreting the gradient program in the context of the operations supplied by the horde-ad library. The value should be the same (after accounting for the 3-tuple represented with binary product) as when evaluating `fooLet` with `crev` on the same input. A shorthand that creates the symbolic derivative program and interprets it with a given input on the default CPU backend is called `rev` and is used exactly the same (but with often much better performance) as `crev`.

```hs
>>> rev fooLet threeSimpleMatrices
(sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
```


# WIP: The examples below are outdated and will be replaced soon using a new API


## Computing Jacobians

-- TODO: we can have vector/matrix/tensor codomains, but not pair codomains
-- until #68 is done;
-- perhaps a vector codomain example, with a 1000x3 Jacobian, would make sense?
-- 2 years later: actually, we can now have TKProduct codomains.

Now let's consider a function from 'R^n` to `R^m'.  We don't want the gradient, but instead the Jacobian.
```hs
-- A function that goes from `R^3` to `R^2`.
foo :: RealFloat a => (a,a,a) -> (a,a)
foo (x,y,z) =
  let w = x * sin y
  in (atan2 z w, z * w)
```
TODO: show how the 2x3 Jacobian emerges from here



## Forall shapes and sizes

An additional feature of this library is a type system for tensor shape arithmetic. The following code is a part of convolutional neural network definition, for which horde-ad computes the gradient of a shape determined by the shape of input data and initial parameters. The compiler is able to infer a lot of tensor shapes, deriving them both from dynamic dimension arguments (the first two lines of parameters to the function) and from static type-level hints. Look at this beauty.
```hs
convMnistTwoS
  kh@SNat kw@SNat h@SNat w@SNat
  c_in@SNat c_out@SNat _n_hidden@SNat batch_size@SNat
    -- integer parameters denoting basic dimensions, with some notational noise
  input              -- input images, shape (batch_size, c_in, h, w)
  (ker1, bias1)      -- layer1 kernel, shape (c_out, c_in, kh+1, kw+1); and bias, shape (c_out)
  (ker2, bias2)      -- layer2 kernel, shape (c_out, c_out, kh+1, kw+1); and bias, shape (c_out)
  ( weightsDense     -- dense layer weights,
                     -- shape (n_hidden, c_out * ((h+kh)/2 + kh)/2, ((w+kw)/2 + kw)/2)
  , biasesDense )    -- dense layer biases, shape (n_hidden)
  ( weightsReadout   -- readout layer weights, shape (10, n_hidden)
  , biasesReadout )  -- readout layer biases (10)
  =                  -- -> output classification, shape (10, batch_size)
  let t1 = convMnistLayerS kh kw
                           h w
                           c_in c_out batch_size
                           ker1 (constant input) bias1
      t2 = convMnistLayerS kh kw
                           (SNat @((h + kh) `Div` 2)) (SNat @((w + kw) `Div` 2))
                           c_out c_out batch_size
                           ker2 t1 bias2
      m1 = mapOuterS reshapeS t2
      m2 = transpose2S m1
      denseLayer = weightsDense <>$ m2 + asColumnS biasesDense
      denseRelu = relu denseLayer
  in weightsReadout <>$ denseRelu + asColumnS biasesReadout
```
But we don't just want the shapes in comments and in runtime expressions; we want them as a compiler-verified documentation in the form of the type signature of the function:
```hs
convMnistTwoS
  :: forall kh kw h w c_in c_out n_hidden batch_size d r.
     ( 1 <= kh             -- kernel height is large enough
     , 1 <= kw             -- kernel width is large enough
     , ADModeAndNum d r )  -- differentiation mode and numeric type are known to the engine
  => -- The two boilerplate lines below tie type parameters to the corresponding
     -- value parameters (built with SNat) denoting basic dimensions.
     SNat kh -> SNat kw -> SNat h -> SNat w
  -> SNat c_in -> SNat c_out -> SNat n_hidden -> SNat batch_size
  -> OS.Array '[batch_size, c_in, h, w] r
  -> ( ADVal d (OS.Array '[c_out, c_in, kh + 1, kw + 1] r)
     , ADVal d (OS.Array '[c_out] r ) )
  -> ( ADVal d (OS.Array '[c_out, c_out, kh + 1, kw + 1] r)
     , ADVal d (OS.Array '[c_out] r) )
  -> ( ADVal d (OS.Array '[ n_hidden
                          , c_out * (((h + kh) `Div` 2 + kh) `Div` 2)
                                  * (((w + kw) `Div` 2 + kw) `Div` 2)
                          ] r)
     , ADVal d (OS.Array '[n_hidden] r) )
  -> ( ADVal d (OS.Array '[10, n_hidden] r)
     , ADVal d (OS.Array '[10] r) )
  -> ADVal d (OS.Array '[10, batch_size] r)
```

The full neural network definition from which this function is taken can be found at

https://github.com/Mikolaj/horde-ad/tree/master/example

in file `MnistCnnShaped.hs` and the directory contains several other sample neural networks for MNIST digit classification. Among them are recurrent, convolutional and fully connected networks based on fully typed tensors (sizes of all dimensions are tracked in the types, as above) as well as weakly typed fully connected networks built with, respectively, matrices, vectors and raw scalars (working with scalars is the most flexible but slowest; all others have comparable performance on CPU).


Compilation from source
-----------------------

Because we use [hmatrix] the OS needs libraries that on Ubuntu/Debian
are called libgsl0-dev, liblapack-dev and libatlas-base-dev.
See https://github.com/haskell-numerics/hmatrix/blob/master/INSTALL.md
for information about other OSes.
Other Haskell packages need their usual C library dependencies,
as well, e.g., package zlib needs C library zlib1g-dev.

For development, copying the included `cabal.project.local.development`
to `cabal.project.local` provides a sensible default to run `cabal build` with.
For extensive testing, a command like

    cabal test minimalTest --enable-optimization -f test_seq

ensures that the code is compiled with optimization and so executes the rather
computation-intensive testsuites in reasonable time.


Running tests
-------------

The test suite can run in parallel but, if so, the PP tests need to be disabled:

    cabal test simplifiedOnlyTest --enable-optimization --test-options='-p "! /PP/"'

Parallel run may cause the extra printf messages coming from within the tests
to be out of order. To keep your screen tidy, simply redirect `stderr`,
e.g. via: `2>/dev/null`:

    cabal test simplifiedOnlyTest --enable-optimization --test-options='-p "! /PP/"' 2>/dev/null

You can also run the test suite sequentially and then all tests can be included
and the extra printf messages are displayed fine most of the time:

    cabal test simplifiedOnlyTest --enable-optimization -f test_seq


Coding style
------------

Stylish Haskell is used for slight auto-formatting at buffer save; see
[.stylish-haskell.yaml](https://github.com/Mikolaj/horde-ad/blob/master/.stylish-haskell.yaml).
As defined in the file, indentation is 2 spaces wide and screen is
80-columns wide. Spaces are used, not tabs. Spurious whitespace avoided.
Spaces around arithmetic operators encouraged.
Generally, relax and try to stick to the style apparent in a file
you are editing. Put big formatting changes in separate commits.

Haddocks should be provided for all module headers and for all functions
and types, or at least main sections, from the most important modules.
Apart of that, only particularly significant functions and types
are distinguished by having a haddock. If minor ones have comments,
they should not be haddocks and they are permitted to describe
implementation details and be out of date. Prefer assertions instead
of comments, unless too verbose.


Copyright
---------

Copyright 2023 Mikolaj Konarski, Well-Typed LLP and others (see git history)

License: BSD-3-Clause (see file LICENSE)



[hmatrix]: https://hackage.haskell.org/package/hmatrix
[orthotope]: https://hackage.haskell.org/package/orthotope
