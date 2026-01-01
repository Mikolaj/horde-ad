{-# LANGUAGE DeriveTraversable #-}
module Data.Bag where


-- | An ordered sequence that can be folded over.
data Bag a = BZero | BOne a | BTwo (Bag a) (Bag a) | BList [Bag a]
  deriving (Show, Functor, Foldable, Traversable)

-- Really only here for 'pure'
instance Applicative Bag where
  pure = BOne
  BZero <*> _ = BZero
  BOne f <*> t = f <$> t
  BTwo f1 f2 <*> t = BTwo (f1 <*> t) (f2 <*> t)
  BList fs <*> t = BList [f <*> t | f <- fs]

instance Semigroup (Bag a) where (<>) = BTwo
instance Monoid (Bag a) where mempty = BZero
