{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
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
import Test.Feat
 
deriveEnumerable ''A
 
data Nat = Zero_nat
         | Suc Nat
         deriving (Eq, Ord, Typeable, Show)
 
deriveEnumerable ''Nat
 
instance Arbitrary Nat where
        arbitrary = sized uniform
 
instance CoArbitrary Nat where
        coarbitrary = coarbitraryShow
 
data Ifex = Cif Bool
          | Vif Nat
          | If Ifex Ifex Ifex
          deriving (Eq, Ord, Typeable, Show)
 
deriveEnumerable ''Ifex
 
instance Arbitrary Ifex where
        arbitrary = sized uniform
 
instance CoArbitrary Ifex where
        coarbitrary = coarbitraryShow
 
data Boolex = Const Bool
            | Var Nat
            | Neg Boolex
            | And Boolex Boolex
            deriving (Eq, Ord, Typeable, Show)
 
deriveEnumerable ''Boolex
 
instance Arbitrary Boolex where
        arbitrary = sized uniform
 
instance CoArbitrary Boolex where
        coarbitrary = coarbitraryShow
 
valif :: Ifex -> (Nat -> Bool) -> Bool
valif (Cif b) env = b
valif (Vif x) env = env x
valif (If b t e) env
  = (if valif b env then valif t env else valif e env)
 
value :: Boolex -> (Nat -> Bool) -> Bool
value (Const b) env = b
value (Var x) env = env x
value (Neg b) env = not (value b env)
value (And b c) env = value b env && value c env
 
bool2if :: Boolex -> Ifex
bool2if (Const b) = Cif b
bool2if (Var x) = Vif x
bool2if (Neg b) = If (bool2if b) (Cif False) (Cif True)
bool2if (And b c) = If (bool2if b) (bool2if c) (Cif False)
main = Prelude.undefined