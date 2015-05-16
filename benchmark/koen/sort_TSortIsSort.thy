theory sort_TSortIsSort
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Tree = TNode "'a Tree" "'a" "'a Tree" | TNil
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun flatten :: "'a Tree => 'a list => 'a list" where
  "flatten (TNode p z q) y = flatten p (Cons2 z (flatten q y))"
  | "flatten (TNil) y = y"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun add :: "int => int Tree => int Tree" where
  "add x (TNode p z q) =
     (if x <= z then TNode (add x p) z q else TNode p z (add x q))"
  | "add x (TNil) = TNode (TNil) x (TNil)"
  fun toTree :: "int list => int Tree" where
  "toTree (Nil2) = TNil"
  | "toTree (Cons2 y xs) = add y (toTree xs)"
  fun tsort :: "int list => int list" where
  "tsort x =
     dot
       (% (y :: (int list => int list)) => y (Nil2))
       (% (z :: int list) =>
          dot
            (% (x2 :: int Tree) => % (x3 :: int list) => flatten x2 x3)
            (% (x4 :: int list) => toTree x4) z)
       x"
  hipster insert2 isort flatten dot add toTree tsort
  theorem x0 :
    "!! (x :: int list) . (tsort x) = (isort x)"
    oops
end
