# horde-ad
Higher Order Reverse Derivatives Efficiently - Automatic Differentiation library based on the paper "Provably correct, asymptotically efficient, higher-order reverse-mode automatic differentiation"

This is very much WIP, both engine and API. For now it can do MNIST digit recognition via fully connected neural networks, but it can also handle exotic variants of such networks that wouldn't express well in a language of matrices and their operations (which we don't have). It can also do all kinds of wild Haskell toy examples but the API is not toy-friendly ATM, see a sample below.

Mature Haskell libraries with similar and greater capabilities, but varying efficiency, are https://hackage.haskell.org/package/ad and https://hackage.haskell.org/package/backprop. We owe them; see https://github.com/Mikolaj/horde-ad/blob/master/CREDITS.md.

Here is an example, with WIP noise visible in notation and comments, of computing the gradient of a function that goes from `R^3` to `R^2`

```Haskell
f (x, y, z) =
   let w = x * sin y
   in (atan2 (z, w), z * x)
```

https://github.com/Mikolaj/horde-ad/blob/bdcc42fadca3b29a1c5ab302c4ada8d3e2fb7ec4/test/TestSingleGradient.hs#L95-L148

The ratio of signal to noise raises once you settle on a scalar type, define a toolbox of functions for the task at hand and start composing the functions.
