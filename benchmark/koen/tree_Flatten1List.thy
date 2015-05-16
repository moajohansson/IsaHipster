theory tree_Flatten1List
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  fun flatten1 :: "('a Tree) list => 'a list" where
  "flatten1 (Nil2) = nil2"
  | "flatten1 (Cons2 (Node (Node x3 x4 x5) x2 q) ps) =
       flatten1 (Cons2 (Node x3 x4 x5) (cons2 (Node (Nil2) x2 q) ps))"
  | "flatten1 (Cons2 (Node (Nil2) x2 q) ps) =
       Cons2 x2 (flatten1 (cons2 q ps))"
  | "flatten1 (Cons2 (Nil2) ps) = flatten1 ps"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun concatMap :: "('t => 't2 list) => 't list => 't2 list" where
  "concatMap x (Nil2) = nil2"
  | "concatMap x (Cons2 z xs) = append (x z) (concatMap x xs)"
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (Cons2 y (Nil2))) (flatten0 q)"
  | "flatten0 (Nil2) = Nil2"
  hipster flatten1 append concatMap flatten0
  theorem x0 :
    "!! (ps :: ('a Tree) list) .
       (flatten1 ps) = (concatMap (% (x :: 'a Tree) => flatten0 x) ps)"
    oops
end
