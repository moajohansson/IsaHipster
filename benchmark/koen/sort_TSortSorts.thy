theory sort_TSortSorts
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = TNode "'a Tree" "'a" "'a Tree" | TNil
  fun flatten :: "'a Tree => 'a list => 'a list" where
  "flatten (TNode p z q) y = flatten p (cons z (flatten q y))"
  | "flatten (TNil) y = y"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (nil) = True"
  | "ordered (cons y (nil)) = True"
  | "ordered (cons y (cons y2 xs)) =
       and2 (y <= y2) (ordered (cons y2 xs))"
  fun add :: "int => int Tree => int Tree" where
  "add x (TNode p z q) =
     (if x <= z then TNode (add x p) z q else TNode p z (add x q))"
  | "add x (TNil) = TNode (TNil) x (TNil)"
  fun toTree :: "int list => int Tree" where
  "toTree (nil) = TNil"
  | "toTree (cons y xs) = add y (toTree xs)"
  fun tsort :: "int list => int list" where
  "tsort x =
     dot
       (% (y :: (int list => int list)) => y (nil))
       (% (z :: int list) =>
          dot
            (% (x2 :: int Tree) => % (x3 :: int list) => flatten x2 x3)
            (% (x4 :: int list) => toTree x4) z)
       x"
  theorem x0 :
    "!! (x :: int list) . ordered (tsort x)"
    oops
end
