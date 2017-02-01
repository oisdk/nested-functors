{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}


module Data.Functor.Nested where

import Data.Traversable
import Data.Functor.Classes
import Data.Semiring
import COntrol.Applicative

data Dim
    = L
    | P Dim

data Nested :: Dim -> (* -> *) -> * -> * where
        Flat :: f a -> Nested 'L f a
        Embd :: f (Nested n f a) -> Nested ('P n) f a

instance Eq1 f =>
         Eq1 (Nested c f) where
    liftEq eq (Flat x) (Flat y) = liftEq eq x y
    liftEq eq (Embd x) (Embd y) = liftEq (liftEq eq) x y

instance (Eq1 f, Eq a) =>
         Eq (Nested c f a) where
    (==) = eq1

instance Ord1 f =>
         Ord1 (Nested c f) where
    liftCompare cmp (Flat x) (Flat y) = liftCompare cmp x y
    liftCompare cmp (Embd x) (Embd y) = liftCompare (liftCompare cmp) x y

instance (Ord1 f, Ord a) =>
         Ord (Nested c f a) where
    compare = compare1

instance Show1 f => Show1 (Nested s f) where
  liftShowsPrec f g d (Flat x) =
      liftShowsPrec f g d x
  liftShowsPrec f g d (Embd x) =
      liftShowsPrec (liftShowsPrec f g) (liftShowList f g) d x

instance (Show1 f, Show a) =>
         Show (Nested s f a) where
    showsPrec = showsPrec1

deriving instance Functor f => Functor (Nested n f)
deriving instance Foldable f => Foldable (Nested n f)
deriving instance Traversable f => Traversable (Nested n f)

embdLast :: Functor f => Nested c f (f a) -> Nested ('P c) f a
embdLast (Flat x) = Embd (fmap Flat x)
embdLast (Embd x) = Embd (fmap embdLast x)

class Expandable (d :: Dim)  where
    liftPure :: (∀ a. a -> f a) -> b -> Nested d f b
    liftApp
        :: Functor f
        => (∀ a b. f (a -> b) -> f a -> f b)
        -> Nested d f (x -> y)
        -> Nested d f x
        -> Nested d f y
    liftTrav
        :: Functor f
        => (∀ a b. (a -> f b) -> t a -> f (t b))
        -> (x -> f y)
        -> Nested d t x
        -> f (Nested d t y)
    transpose :: (Traversable t, Applicative t) => Nested d t a -> Nested d t a

instance Expandable 'L where
    liftPure p = Flat . p
    liftApp a (Flat fs) (Flat xs) = Flat (a fs xs)
    liftTrav t f (Flat x) = fmap Flat (t f x)
    transpose = id

instance Expandable d =>
         Expandable ('P d) where
    liftPure p = Embd . p . liftPure p
    liftApp a (Embd fs) (Embd xs) = Embd (a (fmap (liftApp a) fs) xs)
    liftTrav t f (Embd x) = fmap Embd (t (liftTrav t f) x)
    transpose (Embd x) = embdLast (traverse transpose x)

instance (Expandable d, Applicative t) => Applicative (Nested d t) where
  pure = liftPure pure
  (<*>) = liftApp (<*>)

type (f ~> g) = ∀ a. f a -> g a

liftFmap :: Functor f => (f ~> g) -> Nested c f a -> Nested c g a
liftFmap f (Flat x) = Flat (f x)
liftFmap f (Embd x) = Embd (f (fmap (liftFmap f) x))

imap
    :: (Integral n, Traversable f)
    => (Nested c ((,) n) a -> b) -> Nested c f a -> Nested c f b
imap f (Flat x) =
    Flat
        (snd $
         mapAccumL
             (\acc val ->
                   (acc + 1, f (Flat (acc, val))))
             0
             x)
imap f (Embd x) =
    Embd
        (snd $
         mapAccumL
             (\acc val ->
                   (acc + 1, imap (f . Embd . (,) acc) val))
             0
             x)

flatten :: Monad m => Nested c m a -> m a
flatten (Embd x) = x >>= flatten
flatten (Flat x) = x

instance (Expandable n, Applicative f, Semiring a, Traversable f) => Semiring (Nested n f a) where
  zero = pure zero
  (<+>) = liftA2 (<+>)
  one = imap allEq zero where
    allEq :: (Semiring n) => Nested c ((,) Integer) n -> n
    allEq (Flat (_,x)) = one
    allEq (Embd (x,Flat(y,z))) | x /= y = z
    allEq (Embd (x,Embd(y,z))) | x /= y = zero
    allEq (Embd (_,x)) = allEq x
  (<.>) = matMul
