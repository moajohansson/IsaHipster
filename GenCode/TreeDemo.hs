{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module TreeDemo where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

hd :: forall a. [a] -> a;
hd (x : xs) = x;

data Tree a = Leaf a | Node (Tree a) (Tree a);

mirror :: forall a. Tree a -> Tree a;
mirror (Leaf x) = Leaf x;
mirror (Node l r) = Node (mirror r) (mirror l);

leftmost :: forall a. Tree a -> a;
leftmost (Leaf x) = x;
leftmost (Node l r) = leftmost l;

flat_tree :: forall a. Tree a -> [a];
flat_tree (Leaf x) = [x];
flat_tree (Node l r) = flat_tree l ++ flat_tree r;

rigthmost :: forall a. Tree a -> a;
rigthmost (Leaf x) = x;
rigthmost (Node l r) = rigthmost r;

}
