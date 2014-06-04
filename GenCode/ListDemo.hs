{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ListDemo where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Lst a = Emp | Cons a (Lst a);

app :: forall a. Lst a -> Lst a -> Lst a;
app Emp xs = xs;
app (Cons x xs) ys = Cons x (app xs ys);

rev :: forall a. Lst a -> Lst a;
rev Emp = Emp;
rev (Cons x xs) = app (rev xs) (Cons x Emp);

qrev :: forall a. Lst a -> Lst a -> Lst a;
qrev Emp a = a;
qrev (Cons x xs) a = qrev xs (Cons x a);

}
