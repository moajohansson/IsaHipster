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
 
data Lst a = Emp
           | Cons a (Lst a)
           deriving (Eq, Ord, Typeable, Show)
 
deriveEnumerable ''Lst
 
instance (Enumerable a) => Arbitrary (Lst a) where
        arbitrary = sized uniform
 
instance (Show a) => CoArbitrary (Lst a) where
        coarbitrary = coarbitraryShow
 
app :: forall a . Lst a -> Lst a -> Lst a
app Emp xs = xs
app (Cons x xs) ys = Cons x (app xs ys)
 
rev :: forall a . Lst a -> Lst a
rev Emp = Emp
rev (Cons x xs) = app (rev xs) (Cons x Emp)
 
qrev :: forall a . Lst a -> Lst a -> Lst a
qrev Emp a = a
qrev (Cons x xs) a = qrev xs (Cons x a)
main = Prelude.undefined