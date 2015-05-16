theory sort_TSortPermutes
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Tree = TNode "'a Tree" "'a" "'a Tree" | TNil
  datatype Nat = Z | S "Nat"
  fun flatten :: "'a Tree => 'a list => 'a list" where
  "flatten (TNode q z q2) y = flatten q (Cons2 z (flatten q2 y))"
  | "flatten (TNil) y = y"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun count :: "int => int list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z xs) =
       (if x = z then S (count x xs) else count x xs)"
  fun add :: "int => int Tree => int Tree" where
  "add x (TNode q z q2) =
     (if x <= z then TNode (add x q) z q2 else TNode q z (add x q2))"
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
  hipster flatten dot count add toTree tsort
  theorem x0 :
    "!! (x :: int) (y :: int list) . (count x (tsort y)) = (count x y)"
    oops
end
