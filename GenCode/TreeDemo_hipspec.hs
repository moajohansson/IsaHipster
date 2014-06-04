{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}
module Main where
import Prelude (Ord, Show)
import Prelude
       ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**), (>>=),
        (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
        error, id, return, not, fst, snd, map, filter, concat, concatMap,
        reverse, zip, null, takeWhile, dropWhile, all, any, Integer,
        negate, abs, divMod, String, Bool(True, False),
        Maybe(Nothing, Just))
import qualified Prelude
import HipSpec
import Data.Typeable
import Test.QuickCheck.Gen.Unsafe
import HipSpecifyer.Prelude
import GHC.Generics
 
data Default = Default{default0 ::
                       forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
                         [a] -> a,
                       default1 ::
                       forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
                         Tree a -> Tree a,
                       default2 ::
                       forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
                         Tree a -> a,
                       default3 ::
                       forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
                         Tree a -> [a],
                       default4 ::
                       forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
                         Tree a -> a}
             deriving Typeable
 
instance Arbitrary Default where
        arbitrary
          = do Capture default0 <- capture
               Capture default1 <- capture
               Capture default2 <- capture
               Capture default3 <- capture
               Capture default4 <- capture
               return
                 (Default (default0 arbitrary) (default1 arbitrary)
                    (default2 arbitrary)
                    (default3 arbitrary)
                    (default4 arbitrary))
 
instance Names Default where
        names _ = ["_"]
 
hd ::
   forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
     Default -> [a] -> a
hd defaultVar (x : xs) = x
hd defaultVar v0 = default0 defaultVar v0
 
data Tree a = Leaf a
            | Node (Tree a) (Tree a)
            deriving (Typeable, Generic)
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a) =>
         Arbitrary (Tree a) where
        arbitrary = genericArbitrary
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a) =>
         CoArbitrary (Tree a) where
        coarbitrary = genericCoarbitrary
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a) =>
         Observe (Tree a) where
        observe = genericObserve
 
mirror ::
       forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
         Default -> Tree a -> Tree a
mirror defaultVar (Leaf x) = Leaf x
mirror defaultVar (Node l r)
  = Node (mirror defaultVar r) (mirror defaultVar l)
mirror defaultVar v0 = default1 defaultVar v0
 
leftmost ::
         forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
           Default -> Tree a -> a
leftmost defaultVar (Leaf x) = x
leftmost defaultVar (Node l r) = leftmost defaultVar l
leftmost defaultVar v0 = default2 defaultVar v0
 
flat_tree ::
          forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
            Default -> Tree a -> [a]
flat_tree defaultVar (Leaf x) = [x]
flat_tree defaultVar (Node l r)
  = flat_tree defaultVar l ++ flat_tree defaultVar r
flat_tree defaultVar v0 = default3 defaultVar v0
 
rigthmost ::
          forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
            Default -> Tree a -> a
rigthmost defaultVar (Leaf x) = x
rigthmost defaultVar (Node l r) = rigthmost defaultVar r
rigthmost defaultVar v0 = default4 defaultVar v0
main = Prelude.undefined