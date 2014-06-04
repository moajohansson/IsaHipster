{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Exp where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Expr a b = Cex a | Vex b | Bex (a -> a -> a) (Expr a b) (Expr a b);

hd :: forall a. [a] -> a;
hd (x : xs) = x;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x : xs) = xs;

data Program a b = Done | Const a (Program a b) | Load b (Program a b)
  | Apply (a -> a -> a) (Program a b);

exec :: forall a b. (a -> b) -> Program b a -> [b] -> [b];
exec env Done stack = stack;
exec env (Const c p) stack = exec env p (c : stack);
exec env (Load v p) stack = exec env p (env v : stack);
exec env (Apply b p) stack =
  exec env p (b (hd stack) (hd (tl stack)) : tl (tl stack));

value :: forall a b. (a -> b) -> Expr b a -> b;
value env (Cex c) = c;
value env (Vex v) = env v;
value env (Bex b e1 e2) = b (value env e1) (value env e2);

sequence :: forall a b. Program a b -> Program a b -> Program a b;
sequence Done p = p;
sequence (Const c pa) p = Const c (sequence pa p);
sequence (Load v pa) p = Load v (sequence pa p);
sequence (Apply b pa) p = Apply b (sequence pa p);

compile :: forall a b. Expr a b -> Program a b;
compile (Cex c) = Const c Done;
compile (Vex v) = Load v Done;
compile (Bex b e1 e2) =
  sequence (compile e2) (sequence (compile e1) (Apply b Done));

}
