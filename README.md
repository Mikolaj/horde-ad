# HORDE-AD: Higher Order Reverse Derivatives Efficiently

This is an Automatic Differentiation library based on the paper [_"Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"_](https://dl.acm.org/doi/10.1145/3498710) by Krawiec, Krishnaswami, Peyton Jones, Ellis, Fitzgibbon, and Eisenberg, developed in collaboration with the paper's authors.

This is an early prototype, both in terms of the engine performance and the API augmented with a set of tools and examples. The user should be ready to add missing primitives, as well as any obvious tools that should be predefined but aren't. You can already differentiate all basic neural network architectures, such as fully connected, recurrent, convolutional and residual networks. The library, due to its loose coupling of differentiation and data containers, can naturally handle exotic variants of such networks that wouldn't express well in a limited language of matrices or tensors.

Applications outside machine learning are very much in scope, given that the notion of a neural network is not hardwired into the formalism, but ad hoc redefined from basic building blocks of general automatic differentiation whenever it's needed.

Mature Haskell libraries with similar capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. See also https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md. Benchmarks suggest that horde-ad has competitive performance.
<!--
-- TODO: do and redo the benchmarks

The benchmarks at SOMEWHERE show that this library has performance highly competitive with (i.e. faster than) those and PyTorch on CPU.
-->
It is hoped that the separation of AD logic from matrix and tensor manipulation (deferred to [hmatrix] and [orthotope], respectively) will enable similar speedups on numerical accelerators.


## Computing the derivative of a simple function

Here is an example of a Haskell function to be differentiated:

```hs
-- A function that goes from R^3 to R.
foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w  -- note that w appears twice
```

The gradient of `foo` is:
<!--
TODO: this may yet get simpler and the names not leaking implementation details
("delta") so much, when the adaptor gets used at scale and redone.
Alternatively, we could settle on Double already here.
-->
```hs
grad_foo :: forall r. (HasDelta r, AdaptableScalar 'ADModeGradient r)
         => (r, r, r) -> (r, r, r)
grad_foo = rev @r foo
```

As can be verified by computing the gradient at `(1.1, 2.2, 3.3)`:
```hs
>>> grad_foo (1.1 :: Double, 2.2, 3.3)
(2.4396285219055063, -1.953374825727421, 0.9654825811012627)
```

As a side note, `w` is processed only once during gradient computation and this property of sharing preservation is guaranteed universally by horde-ad without any action required from the user. The property holds not only for scalar values, but for arbitrary tensors, e.g., those in further examples. We won't mention the property further.

<!--
Do we want yet another example here, before we reach Jacobians or shaped tensors? Perhaps one with the testing infrastructure, e.g., generating a single set of random tensors, or a full QuickCheck example or just a simple
```hs
  assertEqualUpToEpsilon 1e-9
    (rev bar (1.1, 2.2, 3.3))
    (6.221706565357043, -12.856908977773593, 6.043601532156671)
```
? Or is there a risk the reader won't make it to the shaped example below if we tarry here? Or perhaps finish the shaped tensor example below with an invocation of `assertEqualUpToEpsilon`?
-->


<!--
## Computing Jacobians

-- TODO: we can have vector/matrix/tensor codomains, but not pair codomains
-- until #68 is done;
-- perhaps a vector codomain example, with a 1000x3 Jacobian, would make sense?

Now let's consider a function from 'R^n` to `R^m'.  We don't want the gradient, but instead the Jacobian.
```hs
-- A function that goes from `R^3` to `R^2`.
foo :: RealFloat a => (a,a,a) -> (a,a)
foo (x,y,z) =
  let w = x * sin y
  in (atan2 z w, z * w)
```
TODO: show how the 2x3 Jacobian emerges from here
-->


# Forall shapes and sizes

An additional feature of this library is a type system for tensor shape arithmetic. The following code is a part of convolutional neural network definition, for which horde-ad computes the gradient of a shape determined by the shape of input data and initial parameters. The compiler is able to infer a lot of tensor shapes, deriving them both from dynamic dimension arguments (the first line of parameters to the function) and from static type-level hints. Look at this beauty.
```hs
convMnistTwoS
  kh@MkSN kw@MkSN h@MkSN w@MkSN c_in@MkSN c_out@MkSN _n_hidden@MkSN batch_size@MkSN
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
                           (MkSN @((h + kh) `Div` 2)) (MkSN @((w + kw) `Div` 2))
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
     -- value parameters (built with MkSN) denoting basic dimensions.
     StaticNat kh -> StaticNat kw -> StaticNat h -> StaticNat w
  -> StaticNat c_in -> StaticNat c_out -> StaticNat n_hidden -> StaticNat batch_size
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
Then a command like

    cabal test minimalTest --enable-optimization --test-options='-p "Simple QuickCheck of gradient vs derivative vs perturbation"'

ensures that the code is compiled with optimization and so executes the rather
computation-intensive testsuite in reasonable time.


Running tests
-------------

The test suite is run in parallel mode by default:

    cabal test shortTestForCI --enable-optimization

However, this may cause extra printf messages from within the tests to be out of order. To keep your screen tidy, simply redirect `stderr`, e.g.: `2>/dev/null`:

    cabal test shortTestForCI --enable-optimization 2>/dev/null

You can also run the test suite sequentially:

    cabal test shortTestForCI --enable-optimization -f test_seq


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
and types from most important modules. Apart of that, only particularly
significant functions and types are distinguished by having a haddock.
If minor ones have comments, they should not be haddocks and they are
permitted to describe implementation details and be out of date.
Prefer assertions instead of comments, unless too verbose.


Copyright
---------

Copyright 2022 Mikolaj Konarski and others (see git history)

License: BSD-3-Clause (see file LICENSE)



[hmatrix]: https://hackage.haskell.org/package/hmatrix
[orthotope]: https://hackage.haskell.org/package/orthotope
