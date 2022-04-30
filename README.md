# horde-ad
Higher Order Reverse Derivatives Efficiently - Automatic Differentiation library based on the paper "Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation" by Faustyna Krawiec, Neel Krishnaswami, Simon Peyton Jones, Tom Ellis, Andrew Fitzgibbon and Richard Eisenberg. Mature Haskell libraries with similar capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. See also https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md.

This is an early prototype, both in terms of the engine performance and the API and toolbox for the library user. The user should be ready to add missing primitives, as well as obvious tools that should be predefined but aren't. One can already build with the library all basic neural network architectures, such as fully connected, recurrent, convolutional and residual networks. The library, due to its loose coupling of differentiation and data containers, can naturally handle exotic variants of such networks that wouldn't express well in a language of matrices or tensors. Applications outside machine learning are plausible, given that the notion of a neural network is not hardwired into the formalism, but ad hoc redefined from basic blocks of general automatic differentiation whenever it's needed, e.g., in the tests and benchmarks of the library.

Here is an example of computing the gradient of a function that goes from `R^3` to `R^2`

```Haskell
f (x, y, z) =
    let w = x * sin y
    in (atan2 (z, w), z * x)
```

https://github.com/Mikolaj/horde-ad/blob/5391d3c7dd8893d6038886f4b77b2adbdc5579a7/test/common/TestSingleGradient.hs#L258-L311

Elsewhere in the same file is a computation of the forward derivative of the function and a QuickCheck test relating it to the gradient. It uses the same definition of the objective function and the same glue code for grouping parameters, etc. The ratio of signal to noise (maths to glue code) is much higher in more complex functions, e.g., neural networks. Several sample neural networks for MNIST digit classification are gathered in

https://github.com/Mikolaj/horde-ad/tree/5391d3c7dd8893d6038886f4b77b2adbdc5579a7/src/HordeAd/Tool

Among them are recurrent, convolutional and fully connected networks based on fully typed tensors (sizes of all dimensions are tracked in the types) as well as weakly typed fully connected networks built with, respectively, matrices, vectors and raw scalars (most flexible but slowest).


Compilation from source
-----------------------

Because we use https://hackage.haskell.org/package/hmatrix,
the OS needs libraries that on Ubuntu/Debian are called
libgsl0-dev, liblapack-dev and libatlas-base-dev.
See https://github.com/haskell-numerics/hmatrix/blob/master/INSTALL.md
for information about other OSes.
Other Haskell packages need their usual C library dependencies,
as well, e.g., package zlib needs C library zlib1g-dev.


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
