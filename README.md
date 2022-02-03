# horde-ad
Higher Order Reverse Derivatives Efficiently - Automatic Differentiation library based on the paper "Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"

This is very much WIP, both engine and API. For now it can do MNIST digit recognition via fully connected neural networks, but it can also handle exotic variants of such networks that wouldn't express well in a language of matrices and their operations. It can also do all kinds of wild Haskell toy examples but the API is not toy-friendly ATM, see a sample below.

Mature Haskell libraries with similar and greater capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. We owe them; see https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md.

Here is an example of computing the gradient of a function that goes from `R^3` to `R^2`

```Haskell
f (x, y, z) =
   let w = x * sin y
   in (atan2 (z, w), z * x)
```

https://github.com/Mikolaj/horde-ad/blob/bdcc42fadca3b29a1c5ab302c4ada8d3e2fb7ec4/test/TestSingleGradient.hs#L95-L148

The WIP noise is visible in notation and in comments. The ratio of signal to noise raises once you settle on a scalar type, define a toolbox of functions for the task at hand and start composing the functions.

Larger examples with the library are the fully connected neural networks for MNIST digit classification constructed using, in turn: [matrices](https://github.com/Mikolaj/horde-ad/blob/delta-vector/src/HordeAd/MnistToolsMatrix.hs), [vectors](https://github.com/Mikolaj/horde-ad/blob/delta-vector/src/HordeAd/MnistToolsVector.hs) and [scalars](https://github.com/Mikolaj/horde-ad/blob/delta-vector/src/HordeAd/MnistToolsScalar.hs).


Compilation from source
-----------------------

Because we use https://hackage.haskell.org/package/hmatrix,
the OS needs libraries that on Ubuntu/Debian are called
libgsl0-dev, liblapack-dev and libatlas-base-dev.
See https://github.com/haskell-numerics/hmatrix/blob/master/INSTALL.md
for information about other OSes.


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
