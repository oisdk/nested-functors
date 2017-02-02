{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module Main (main) where

import Test.QuickCheck
import Test.DocTest
import Data.Functor.Nested
import Test.Semiring
import Data.Functor.Classes

instance (Arbitrary a, Applicative f, Expandable d) =>
         Arbitrary (Nested d f a) where
    arbitrary = liftMake (fmap pure) arbitrary

infixr 5 :-
data Vect d a where
  One  :: a -> Vect 'L a
  (:-) :: a -> Vect n a -> Vect ('P n) a

instance Functor (Vect d) where
  fmap f (One x) = One (f x)
  fmap f (x :- xs) = f x :- fmap f xs

class App n where
  mk :: a -> Vect n a

instance App 'L where
  mk = One

instance App n => App ('P n) where
  mk x = x :- mk x

zipWithV :: (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWithV f (One x) (One y) = One (f x y)
zipWithV f (x :- xs) (y :- ys) = f x y :- zipWithV f xs ys

instance App n => Applicative (Vect n) where
  pure = mk
  (<*>) = zipWithV ($)

instance Foldable (Vect n) where
  foldr f b (One x) = f x b
  foldr f b (x :- xs) = f x (foldr f b xs)

instance Traversable (Vect n) where
  traverse f (One x) = fmap One (f x)
  traverse f (x :- xs) = (:-) <$> f x <*> traverse f xs

instance Show1 (Vect n) where
  liftShowsPrec f g d = liftShowsPrec f g d . foldr (:) []

instance Show a => Show (Vect n a) where
  showsPrec = showsPrec1

instance Eq1 (Vect n) where
  liftEq eq xs ys = and (zipWithV eq xs ys)

instance Testable (Either String a) where
  property = either (`counterexample` False) (const (property True))

type UnaryLaws a = a -> Either String String
type BinaryLaws a = a -> a -> Either String String
type TernaryLaws a = a -> a -> a -> Either String String

main :: IO ()
main = do
  quickCheck (unaryLaws   :: UnaryLaws   (Nested ('P 'L) (Vect ('P 'L)) Integer))
  quickCheck (binaryLaws  :: BinaryLaws  (Nested ('P 'L) (Vect ('P 'L)) Integer))
  quickCheck (ternaryLaws :: TernaryLaws (Nested ('P 'L) (Vect ('P 'L)) Integer))
  quickCheck (unaryLaws   :: UnaryLaws   (Nested ('P 'L) (Vect ('P ('P 'L))) Integer))
  quickCheck (binaryLaws  :: BinaryLaws  (Nested ('P 'L) (Vect ('P ('P 'L))) Integer))
  quickCheck (ternaryLaws :: TernaryLaws (Nested ('P 'L) (Vect ('P ('P 'L))) Integer))
  doctest [ "-isrc", "src/" ]
