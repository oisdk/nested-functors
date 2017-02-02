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
import Control.Applicative
import Data.Functor.Identity

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

class Expandable (c :: Dim)  where
    liftMake
        :: Functor f
        => (forall a. f a -> f (v a)) -> f b -> f (Nested c v b)
    liftAp
        :: Applicative f
        => Nested c f (a -> b) -> Nested c f a -> Nested c f b
    transpose
        :: (Applicative f, Traversable f)
        => Nested c f a -> Nested c f a
    matMul
        :: (Semiring a, Applicative f, Traversable f)
        => Nested c f a -> Nested c f a -> Nested c f a
    mul1
        :: (Applicative f, Traversable f, Semiring a)
        => Nested c f a -> f (Nested c f a) -> Nested c f a


getEmbd :: Nested ('P n) f a -> f (Nested n f a)
getEmbd (Embd x) = x

instance Expandable 'L where
    liftMake f x = fmap Flat (f x)
    liftAp (Flat fs) (Flat xs) = Flat ((<*>) fs xs)
    transpose (Flat x) = Flat x
    matMul (Flat xs) (Flat ys) = Flat (liftA2 (<.>) xs ys)
    mul1 (Flat xs) ys =
        Flat $
        fmap
            (\(Flat yr) ->
                  add $ liftA2 (<.>) xs yr)
            ys

instance (Expandable n) =>
         Expandable ('P n) where
    liftMake f x = fmap Embd (f (liftMake f x))
    liftAp (Embd fs) (Embd xs) = Embd (liftA2 liftAp fs xs)
    transpose (Embd x) = embdLast (traverse transpose x)
    matMul (Embd xs) y =
        case transpose y of
            Embd ys -> Embd (fmap (`mul1` ys) xs)
    mul1 (Embd x) y = Embd (mull x (fmap getEmbd y))

instance (Applicative f, Expandable c) =>
         Applicative (Nested c f) where
    pure x = runIdentity (liftMake (fmap pure) (Identity x))
    (<*>) = liftAp

mull
    :: (Applicative f, Traversable f, Semiring a, Expandable n)
    => f (Nested n f a) -> f (f (Nested n f a)) -> f (Nested n f a)
mull xr = fmap (add . liftA2 (<.>) xr)


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

instance (Expandable n, Applicative f, Semiring a, Traversable f) =>
         Semiring (Nested n f a) where
    zero = pure zero
    (<+>) = liftA2 (<+>)
    one = imap allEq zero
      where
        allEq
            :: (Semiring n)
            => Nested c ((,) Integer) n -> n
        allEq (Flat (_,_)) = one
        allEq (Embd (x,Flat (y,z)))
          | x /= y = z
        allEq (Embd (x,Embd (y,_)))
          | x /= y = zero
        allEq (Embd (_,x)) = allEq x
    (<.>) = matMul
