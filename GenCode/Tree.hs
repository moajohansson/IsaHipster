{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Tree where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Tree a = Leaf a | Node (Tree a) (Tree a);

mapa :: forall a b. (a -> b) -> Tree a -> Tree b;
mapa f (Leaf x) = Leaf (f x);
mapa f (Node l r) = Node (mapa f l) (mapa f r);

mirror :: forall a. Tree a -> Tree a;
mirror (Leaf x) = Leaf x;
mirror (Node l r) = Node (mirror r) (mirror l);

}
