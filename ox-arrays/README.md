## ox-arrays

ox-arrays is an array library that defines nested arrays, including tuples, of
(eventually) unboxed values. The arrays are represented in struct-of-arrays
form via the `Data.Vector.Unboxed` data family trick; the component arrays are
`orthotope` arrays
([RankedS](https://hackage.haskell.org/package/orthotope-0.1.7.0/docs/Data-Array-RankedS.html))
which describe elements using a _stride vector_ or
[LMAD](https://dl.acm.org/doi/pdf/10.1145/509705.509708) so that `transpose`
and `replicate` need only modify array metadata, not actually move around data.

Because of the struct-of-arrays representation, nested arrays are not fully
general: indeed, arrays are not actually nested under the hood, so if one has an
array of arrays, those element arrays must all have the same shape (length,
width, etc.). If one has an array of tuples of arrays, then all the `fst`
components must have the same shape and all the `snd` components must have the
same shape, but the two pair components themselves can be different.

However, the nesting functionality of ox-arrays can be completely ignored if you
only care about other parts of its API, or the vectorised arithmetic operations
(using hand-written C code). Nesting support mostly does not get in the way, and
has essentially no overhead (both when it's used and when it's not used).

ox-arrays defines three array types: `Ranked`, `Shaped` and `Mixed`.
- `Ranked` corresponds to `orthotope`'s
  [RankedS](https://hackage.haskell.org/package/orthotope-0.1.7.0/docs/Data-Array-RankedS.html)
  and has the _rank_ of the array (its number of dimensions) on the type level.
  For example, `Ranked 2 Float` is a two-dimensional array of `Float`s, i.e. a
  matrix.
- `Shaped` corresponds to `orthotope`'s
  [ShapedS](https://hackage.haskell.org/package/orthotope-0.1.7.0/docs/Data-Array-ShapedS.html).
  and has the full _shape_ of the array (its dimension sizes) on the type level
  as a type-level list of `Nat`s. For example, `Shaped [2,3] Float` is a 2-by-3
  matrix. The innermost dimension correspond to the right-most element in the
  list.
- `Mixed` is halfway between the two: it has a type parameter of kind
  `[Maybe Nat]` whose length is the rank of the array; `Nothing` elements have
  unknown size, whereas `Just` elements have the indicated size. The type
  `Mixed [Nothing, Nothing] a` is equivalent to `Ranked 2 a`; the type
  `Mixed [Just n, Just m] a` is equivalent to `Shaped [n, m] a`.

In various places in the API of a library like ox-arrays, one can make a
decision between 1. requiring a type class constraint providing certain
information (e.g.
[KnownNat](https://hackage.haskell.org/package/base-4.21.0.0/docs/GHC-TypeLits.html#t:KnownNat)
or `orthotope`'s
[Shape](https://hackage.haskell.org/package/orthotope-0.1.7.0/docs/Data-Array-ShapedS.html#t:Shape)),
or 2. taking singleton _values_ that encode said information in a way that is
linked to the type level (e.g.
[SNat](https://hackage.haskell.org/package/base-4.21.0.0/docs/GHC-TypeLits.html#t:SNat)).
`orthotope` chooses the type class approach; ox-arrays chooses the singleton
approach. Singletons are more verbose at times, but give the programmer more
insight in what data is flowing where, and more importantly, more control: type
class inference is very nice and implicit, but if it's not powerful enough for
the trickery you're doing, you're out of luck. Singletons allow you to explain
as precisely as you want to GHC what exactly you're doing.

Below the surface layer, there is a more low-level wrapper (`XArray`) around
`orthotope` that defines a non-nested `Mixed`-style array type.

**Be aware**: `ox-arrays` attempts to preserve sharing as much as possible.
That is to say: if a function is able to avoid copying array data and return an
array that references the original underlying `Vector`, it may do so. For
example, this means that if you convert a nested array to a list of arrays, all
returned arrays reference part of the original array without copying. This
makes `mtoList` fast, but also means that memory may be retained longer than
you might expect.

Here is a little taster of the API, to get a sense for the design:

```haskell
import GHC.TypeLits (Nat, SNat)

data Ranked (n :: Nat) a             {- e.g. -}  Ranked 3 Float
data Shaped (sh :: '[Nat]) a         {- e.g. -}  Shaped [2,3,4] Float
data Mixed (xsh :: '[Maybe Nat]) a   {- e.g. -}  Mixed [Just 2, Nothing, Just 4] Float

-- Shape types are written Sh{R,S,X}. The 'I' prefix denotes a Int-filled shape;
-- ShR and ShX are more general containers. ShS is a singleton.
rshape :: Elt a => Ranked n a  -> IShR n
sshape :: Elt a => Shaped sh a -> ShS sh
mshape :: Elt a => Mixed xsh a -> IShX xsh

-- Index types are written Ix{R,S,X}.
rindex :: Elt a => Ranked n a  -> IIxR n   -> a
sindex :: Elt a => Shaped sh a -> IIxS sh  -> a
mindex :: Elt a => Mixed xsh a -> IIxX xsh -> a

-- The index types can be used as if they were defined as follows; pattern
-- synonyms are provided to construct the illusion. (The actual definitions are
-- a bit more general and indirect.)
data IIxR n where
  ZIR   :: IIxR 0
  (:.:) :: Int -> IIxR n -> IIxR (n + 1)

data IIxS sh where
  ZIS   :: IIxS '[]
  (:.$) :: Int -> IIxS sh -> IIxS (n : sh)

data IIxX xsh where
  ZIX   :: IIxX '[]
  (:.%) :: Int -> IIxX xsh -> IIxX (mn : xsh)

-- Similarly, the shape types can be used as if they were defined as follows.
data IShR n where
  ZSR   :: IShR 0
  (:$:) :: Int -> IShR n -> IShR (n + 1)

data ShS sh where
  ZSS   :: ShS '[]
  (:$$) :: SNat n -> ShS sh -> ShS (n : sh)

data IShX xsh where
  ZSX   :: IShX '[]
  (:$%) :: SMayNat Int mn -> IShX xsh -> IShX (mn : xsh)
-- where:
data SMayNat i n where
  SUnknown :: i   -> SMayNat i Nothing
  SKnown   :: SNat n -> SMayNat i (Just n)

-- Occasionally one needs a singleton for only the _known_ dimensions of a mixed
-- shape -- that is to say, only the statically-known part of a mixed shape.
-- StaticShX provides for this need. It can be used as if defined as follows:
data StaticShX xsh where
  ZKX   :: StaticShX '[]
  (:!%) :: SMayNat () mn -> StaticShX xsh -> StaticShX (mn : xsh)

-- The Elt class describes types that can be used as elements of an array. While
-- it is technically possible to define new instances of this class, typical
-- usage should regard Elt as closed. The user-relevant instances are the
-- following:
class Elt a
instance                   Elt ()
instance                   Elt Bool
instance                   Elt Float
instance                   Elt Double
instance                   Elt Int
instance (Elt a, Elt b) => Elt (a, b)
instance Elt a          => Elt (Ranked n a)
instance Elt a          => Elt (Shaped sh a)
instance Elt a          => Elt (Mixed xsh a)

-- Essentially all functions that ox-arrays offers on arrays are first-order:
-- add two arrays elementwise, transpose an array, append arrays, compute
-- minima/maxima, zip/unzip, nest/unnest, etc. The first-order approach allows
-- operations, especially arithmetic ones, to be vectorised using hand-written
-- C code, without needing any sort of JIT compilation.
rappend :: Elt a => Ranked (n + 1) a  -> Ranked (n + 1) a  -> Ranked (n + 1) a
sappend :: Elt a => Shaped (n : sh) a -> Shaped (m : sh) a -> Shaped (n + m : sh) a
mappend :: Elt a => Mixed (n : sh) a  -> Mixed (m : sh) a  -> Mixed (AddMaybe n m : sh) a

-- Exceptionally, also one higher-order function is provided per array type:
-- 'generate'. These functions have the caveat that regularity of arrays must be
-- preserved: all returned 'a's must have equal shape. See the documentation of
-- 'mgenerate'.
-- Warning: because the invocations of the function you pass cannot be
-- vectorised, 'generate' is rather slow if 'a' is small.
-- The 'KnownElt' class captures an API infelicity where constraint-based shape
-- passing is the only practical option.
rgenerate :: KnownElt a => IShR n   -> (IxR n   -> a) -> Ranked n a
sgenerate :: KnownElt a => ShS sh   -> (IxS sh  -> a) -> Shaped sh a
mgenerate :: KnownElt a => IShX xsh -> (IxX xsh -> a) -> Mixed xsh a

-- Under the hood, Ranked and Shaped are both newtypes over Mixed. Mixed itself
-- is a data family over XArray, which is a newtype over orthotope's RankedS.
newtype Ranked n  a = Ranked (Mixed (Replicate n Nothing) a)
newtype Shaped sh a = Shaped (Mixed (MapJust sh)          a)
```

About the name: when importing `orthotope` array modules, a possible naming
convention is to use qualified imports as `OR` for "orthotope ranked" arrays and
`OS` for "orthotope shaped" arrays. ox-arrays was started to fill the `OX` gap,
then grew out of proportion.
