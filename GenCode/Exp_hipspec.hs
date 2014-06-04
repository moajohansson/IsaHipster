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
                         [a] -> [a],
                       default2 ::
                       forall a b .
                         (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
                          CoArbitrary b, Typeable b, Observe b) =>
                         (a -> b) -> Program b a -> [b] -> [b],
                       default3 ::
                       forall a b .
                         (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
                          CoArbitrary b, Typeable b, Observe b) =>
                         (a -> b) -> Expr b a -> b,
                       default4 ::
                       forall a b .
                         (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
                          CoArbitrary b, Typeable b, Observe b) =>
                         Program a b -> Program a b -> Program a b,
                       default5 ::
                       forall a b .
                         (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
                          CoArbitrary b, Typeable b, Observe b) =>
                         Expr a b -> Program a b}
             deriving Typeable
 
instance Arbitrary Default where
        arbitrary
          = do Capture default0 <- capture
               Capture default1 <- capture
               Capture default2 <- capture
               Capture default3 <- capture
               Capture default4 <- capture
               Capture default5 <- capture
               return
                 (Default (default0 arbitrary) (default1 arbitrary)
                    (default2 arbitrary)
                    (default3 arbitrary)
                    (default4 arbitrary)
                    (default5 arbitrary))
 
instance Names Default where
        names _ = ["_"]
 
data Expr a b = Cex a
              | Vex b
              | Bex (a -> a -> a) (Expr a b) (Expr a b)
              deriving (Typeable, Generic)
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a,
          Arbitrary b, CoArbitrary b, Observe b, Typeable b) =>
         Arbitrary (Expr b a) where
        arbitrary = genericArbitrary
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a,
          Arbitrary b, CoArbitrary b, Observe b, Typeable b) =>
         CoArbitrary (Expr b a) where
        coarbitrary = genericCoarbitrary
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a,
          Arbitrary b, CoArbitrary b, Observe b, Typeable b) =>
         Observe (Expr b a) where
        observe = genericObserve
 
hd ::
   forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
     Default -> [a] -> a
hd defaultVar (x : xs) = x
hd defaultVar v0 = default0 defaultVar v0
 
tl ::
   forall a . (Arbitrary a, CoArbitrary a, Typeable a, Observe a) =>
     Default -> [a] -> [a]
tl defaultVar [] = []
tl defaultVar (x : xs) = xs
tl defaultVar v0 = default1 defaultVar v0
 
data Program a b = Done
                 | Const a (Program a b)
                 | Load b (Program a b)
                 | Apply (a -> a -> a) (Program a b)
                 deriving (Typeable, Generic)
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a,
          Arbitrary b, CoArbitrary b, Observe b, Typeable b) =>
         Arbitrary (Program b a) where
        arbitrary = genericArbitrary
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a,
          Arbitrary b, CoArbitrary b, Observe b, Typeable b) =>
         CoArbitrary (Program b a) where
        coarbitrary = genericCoarbitrary
 
instance (Arbitrary a, CoArbitrary a, Observe a, Typeable a,
          Arbitrary b, CoArbitrary b, Observe b, Typeable b) =>
         Observe (Program b a) where
        observe = genericObserve
 
exec ::
     forall a b .
       (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
        CoArbitrary b, Typeable b, Observe b) =>
       Default -> (a -> b) -> Program b a -> [b] -> [b]
exec defaultVar env Done stack = stack
exec defaultVar env (Const c p) stack
  = exec defaultVar env p (c : stack)
exec defaultVar env (Load v p) stack
  = exec defaultVar env p (env v : stack)
exec defaultVar env (Apply b p) stack
  = exec defaultVar env p
      (b (hd defaultVar stack) (hd defaultVar (tl defaultVar stack)) :
         tl defaultVar (tl defaultVar stack))
exec defaultVar v0 v1 v2 = default2 defaultVar v0 v1 v2
 
value ::
      forall a b .
        (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
         CoArbitrary b, Typeable b, Observe b) =>
        Default -> (a -> b) -> Expr b a -> b
value defaultVar env (Cex c) = c
value defaultVar env (Vex v) = env v
value defaultVar env (Bex b e1 e2)
  = b (value defaultVar env e1) (value defaultVar env e2)
value defaultVar v0 v1 = default3 defaultVar v0 v1
 
sequence ::
         forall a b .
           (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
            CoArbitrary b, Typeable b, Observe b) =>
           Default -> Program a b -> Program a b -> Program a b
sequence defaultVar Done p = p
sequence defaultVar (Const c pa) p
  = Const c (sequence defaultVar pa p)
sequence defaultVar (Load v pa) p
  = Load v (sequence defaultVar pa p)
sequence defaultVar (Apply b pa) p
  = Apply b (sequence defaultVar pa p)
sequence defaultVar v0 v1 = default4 defaultVar v0 v1
 
compile ::
        forall a b .
          (Arbitrary a, CoArbitrary a, Typeable a, Observe a, Arbitrary b,
           CoArbitrary b, Typeable b, Observe b) =>
          Default -> Expr a b -> Program a b
compile defaultVar (Cex c) = Const c Done
compile defaultVar (Vex v) = Load v Done
compile defaultVar (Bex b e1 e2)
  = sequence defaultVar (compile defaultVar e2)
      (sequence defaultVar (compile defaultVar e1) (Apply b Done))
compile defaultVar v0 = default5 defaultVar v0
main = Prelude.undefined