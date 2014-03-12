{-# LANGUAGE DeriveFunctor, FlexibleInstances, TypeOperators, ScopedTypeVariables, FlexibleContexts #-}
module GenericArbitrary where

import Test.QuickCheck
import GHC.Generics
import Data.Typeable
import Control.Monad

-- Generate a value generically.
genericArbitrary :: forall a. (Typeable a, Arbitrary a, Generic a, GArbitrary (Rep a)) => Gen a
genericArbitrary =
  sized $ \n ->
    -- If the size is 0, only consider non-recursive constructors.
    if n > 0
    then oneof (map gen constructors)
    else oneof (map gen (filter (not . recursive) constructors))
  where
    constructors = map (fmap to) (garbitrary (arbitrary :: Gen a))
    recursive b = recursion b > 0

-- Generating random values of a datatype
class GArbitrary f where
  -- Argument is a generator for the datatype itself, which will be used
  -- when the datatype is recursive
  garbitrary :: Typeable a => Gen a -> [Constr (f b)]

-- Generating random constructors
class GConstr f where
  gconstructor :: Typeable a => Gen a -> Constr (f b)

-- Represents a generator for one constructor of a datatype
data Constr a = Constr {
  -- The generator itself
  gen :: Gen a,
  -- Is the constructor recursive and if so, how many times does the datatype appear
  recursion :: Int
  } deriving Functor

-- Interesting typeclass instances

instance GConstr f => GArbitrary (C1 c f) where
  -- This is the generator for a single constructor.
  -- We have to resize the "recursive generator" depending on how many
  -- times the datatype appears recursively in the constructor
  garbitrary gen = [b]
    where
      b = gconstructor (sized $ \m -> resize (newSize m) gen)
      newSize m
        | recursion b == 1 = m-1
        | otherwise = m `div` recursion b

instance (Typeable a, Arbitrary a) => GConstr (K1 i a) where
  -- An argument to a constructor: see if the argument is recursive or not
  gconstructor gen =
    case gcast gen of
      Nothing ->
        -- Not recursive: use normal generator
        Constr (fmap K1 arbitrary) 0
      Just gen' ->
        -- Recursive: use recursive generator
        Constr (fmap K1 gen') 1

instance (GConstr f, GConstr g) => GConstr (f :*: g) where
  -- A constructor with several arguments: add up the number of recursive occurrences
  gconstructor gen = Constr (liftM2 (:*:) g1 g2) (r1 + r2)
    where
      Constr g1 r1 = gconstructor gen
      Constr g2 r2 = gconstructor gen

-- Generic drivel that doesn't really do anything.
instance GConstr f => GConstr (M1 i c f) where
  gconstructor gen = fmap M1 (gconstructor gen)

instance GConstr U1 where
  gconstructor _ = Constr (return U1) 0

instance (GArbitrary f, GArbitrary g) => GArbitrary (f :+: g) where
  garbitrary gen = map (fmap L1) (garbitrary gen) ++ map (fmap R1) (garbitrary gen)

instance GArbitrary f => GArbitrary (D1 c f) where
  garbitrary gen = map (fmap M1) (garbitrary gen)

-- All the same but for coarbitrary. Sigh...
genericCoarbitrary :: (Generic a, GCoarbitrary (Rep a)) => a -> Gen b -> Gen b
genericCoarbitrary x = gcoarbitrary (from x)

class GCoarbitrary f where
  gcoarbitrary :: f a -> Gen b -> Gen b

instance (GCoarbitrary f, GCoarbitrary g) => GCoarbitrary (f :*: g) where
  gcoarbitrary (x :*: y) = gcoarbitrary x . gcoarbitrary y

instance (GCoarbitrary f, GCoarbitrary g) => GCoarbitrary (f :+: g) where
  gcoarbitrary (L1 x) = variant 0 . gcoarbitrary x
  gcoarbitrary (R1 x) = variant 1 . gcoarbitrary x

instance CoArbitrary a => GCoarbitrary (K1 i a) where
  gcoarbitrary (K1 x) = coarbitrary x

instance GCoarbitrary U1 where
  gcoarbitrary U1 = id

instance GCoarbitrary f => GCoarbitrary (M1 i c f) where
  gcoarbitrary (M1 x) = gcoarbitrary x
