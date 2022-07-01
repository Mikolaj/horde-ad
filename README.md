# HORDE-AD: Higher Order Reverse Derivatives Efficiently 

This is an Automatic Differentiation library based on the paper _"Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"_ by Krawiec, Krishnaswami, Peyton Jones, Ellis, Fitzgibbon, and Eisenberg.

This is an early prototype, both in terms of the engine performance and the API and toolbox for the library user. The user should be ready to add missing primitives, as well as obvious tools that should be predefined but aren't. One can already build with the library all basic neural network architectures, such as fully connected, recurrent, convolutional and residual networks. The library, due to its loose coupling of differentiation and data containers, can naturally handle exotic variants of such networks that wouldn't express well in a language of matrices or tensors. 

Applications outside machine learning are very much in scope, given that the notion of a neural network is not hardwired into the formalism, but ad hoc redefined from basic blocks of general automatic differentiation whenever it's needed.

Mature Haskell libraries with similar capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. See also https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md.  
The benchmarks at TODO show that this library has performance highly competitive with (i.e. faster than) those and PyTorch on CPU.  
It is hoped that the separation of AD logic from matrix and tensor manipulation (deferred to [hmatrix] and [orthotope]) will enable similar speedups on numerical accelerators.

## Computing the derivative of a simple function

Here is an example of computing the gradient of a function that goes from `R^3` to `R`:

```Haskell
-- A function that goes from `R^3` to `R`. 
-- [Arguments are tupled, could just as easily be curried. -awf]
foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) = 
  let w = x * sin y 
  in atan2 z w + z * w  -- [note extra w, we *want* to require returnLet up front --awf] 
```

In order to compute the gradient, we transform the function in the classic manner for forward-mode AD, to take `DualNumber` variables, 
and the `DualMonad` which implements the system in the paper
```Haskell
fooM :: DualMonad d r m 
     => DualNumberVariables d r -> m (DualNumber d r) 
fooM variables = do { 
     let x : y : z : _ = vars variables 
     w <- x * sin y 
     returnLet $ (atan2 z w + z * w)  -- [note extra w, we *want* to require returnLet up front --awf] 
   }
```
We hope to automate this transfomation soon, automatically generating `fooM` from `foo`, but for now it's a mechanical, if somewhat tedious, manual task.

And then the gradient of `foo` is
```Haskell
grad_foo :: HasDelta r => Domain0 r -> (Domain0 r, r) 
grad_foo ds = 
   let ((result, _, _, _), value) = 
         dReverse 1 fooM (ds, V.empty, V.empty, V.empty) 
   in (result, value) 
```

As can be verified by computing the gradient at `(1.1,2.2,3.3)`:
```Haskell
>>> grad_foo (mkDual [1.1, 2.2, 3.3])
[7.75, 1.23, 5.52]
```

## Computing Jacobians.
Now let's consider a function from 'R^n -> R^m'.  We don't want the gradient, but instead the Jacobian.
```Haskell
-- A function that goes from `R^3` to `R^2`. 
foo :: RealFloat a => (a,a,a) -> (a,a)
foo (x,y,z) = 
  let w = x * sin y 
  in (atan2 z w, z * w)
```
TODO: show how the 2x3 Jacobian emerges from here

# Forall shapes and sizes

An additional feature of this library is a type system for tensor shape arithmetic.  Look at this beauty.
```Haskell
convMnistTwoS x                                 -- input images, shape (batch_size, c_in, h, w)
              ker1 bias1                        -- layer1 kernel, shape (c_out, c_in, kh+1, kw+1); and bias, shape (c_out)
              ker2 bias2                        -- layer2 kernel, shape (c_out, c_out, kh+1, kw+1); and bias, shape (c_out)
              weigthsDense                      -- dense weights shape (n_hidden, c_out, ((h+kh)/2 + kh)/2, ((w+kw)/2 + kw)/2) 
              biasesDense                       -- dense biases shape (n_hidden)
              weigthsReadout biasesReadout      -- readout layer weights (10, n_hidden) and bias (10)
              =                                 --> output (10, batch_size)
  do
  t1 <- convMnistLayerS ker1 (constant x) bias1
  t2 <- convMnistLayerS ker2 t1 bias2
  let m1 = mapS reshapeS t2
      m2 = from2S (transpose2 (fromS2 m1))  -- TODO: add permuation transposeS
      denseLayer = weigthsDense <>$ m2 + asColumnS biasesDense
  denseRelu <- reluAct denseLayer
  returnLet $ weigthsReadout <>$ denseRelu + asColumnS biasesReadout
```
But we don't just want the shapes in comments, we want them in the type system:
```Haskell
convMnistTwoS
  :: forall kh kw num_hidden c_out h w c_in batch_size d r m.
     ( KnownNat kh, KnownNat kw, KnownNat num_hidden, KnownNat c_out, KnownNat h, KnownNat w, KnownNat batch_size
     , c_in ~ 1 -- greyscale
     , 1 <= kh  -- kh greater than 1
     , 1 <= kw  -- kw greater than 1
     , DualMonad d r m )
  => OS.Array '[batch_size, c_in, h, w] r
  -> DualNumber d (OS.Array '[ c_out, c_in , kh + 1, kw + 1 ] r)
  -> DualNumber d (OS.Array '[c_out] r)
  -> DualNumber d (OS.Array '[ c_out, c_out, kh + 1, kw + 1 ] r)
  -> DualNumber d (OS.Array '[c_out] r)
  -> DualNumber d (OS.Array '[ num_hidden, c_out,
                                 GHC.TypeLits.* ((h + kh) `Div` 2 + kh) `Div` 2
                                 GHC.TypeLits.* ((w + kw) `Div` 2 + kw) `Div` 2 -- [buglet? kh->kw? -awf]
                             ] r)
  -> DualNumber d (OS.Array '[num_hidden] r)
  -> DualNumber d (OS.Array '[10, num_hidden] r)
  -> DualNumber d (OS.Array '[10] r)
  -> m (DualNumber d (OS.Array '[10, batch_size] r))
```

Several sample neural networks for MNIST digit classification are gathered in

https://github.com/Mikolaj/horde-ad/tree/master/src/HordeAd/Tool

Among them are recurrent, convolutional and fully connected networks based on fully typed tensors (sizes of all dimensions are tracked in the types) as well as weakly typed fully connected networks built with, respectively, matrices, vectors and raw scalars (most flexible but slowest).


# Derivative checking

Elsewhere in the same file is a computation of the forward derivative of the function and a QuickCheck test relating it to the gradient. It uses the same definition of the objective function and the same glue code for grouping parameters, etc. The ratio of signal to noise (maths to glue code) is much higher in more complex functions, e.g., neural networks. 

Compilation from source
-----------------------

Because we use https://hackage.haskell.org/package/hmatrix,
the OS needs libraries that on Ubuntu/Debian are called
libgsl0-dev, liblapack-dev and libatlas-base-dev.
See https://github.com/haskell-numerics/hmatrix/blob/master/INSTALL.md
for information about other OSes.
Other Haskell packages need their usual C library dependencies,
as well, e.g., package zlib needs C library zlib1g-dev.

For development, copying the included `cabal.project.local.development`
to `cabal.project.local` provides a sensible default to run `cabal build` with.
Then a command like

    cabal test minimalTest --enable-optimization --test-options='-p "Simple QuickCheck of gradient vs derivative vs perturbation"'

ensures that the code is compiled with opimization and so executes the rather
computation-intensive testsuite in reasonable time.


Running tests
-------------

The test suite is run in parallel mode by default:

    cabal test shortTestForCI    --enable-optimization

However, this may cause extra printf messages from within the tests to be out of order. To keep your screen tidy, simply redirect `stderr`, e.g.: `2>/dev/null`:

    cabal test shortTestForCI    --enable-optimization 2>/dev/null

You can also run the test suite sequentially:

    cabal test shortTestForCI    --enable-optimization -f test_seq


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
