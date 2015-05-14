theory tree_Flatten1List
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  fun flatten1 :: "('a Tree) list => 'a list" where
  "flatten1 (nil) = nil"
  | "flatten1 (cons (Node (Node x3 x4 x5) x2 q) ps) =
       flatten1 (cons (Node x3 x4 x5) (cons (Node (Nil2) x2 q) ps))"
  | "flatten1 (cons (Node (Nil2) x2 q) ps) =
       cons x2 (flatten1 (cons q ps))"
  | "flatten1 (cons (Nil2) ps) = flatten1 ps"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun concatMap :: "('t => 't2 list) => 't list => 't2 list" where
  "concatMap x (nil) = nil"
  | "concatMap x (cons z xs) = append (x z) (concatMap x xs)"
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (cons y (nil))) (flatten0 q)"
  | "flatten0 (Nil2) = nil"
  theorem x0 :
    "!! (ps :: ('a Tree) list) .
       (flatten1 ps) = (concatMap (% (x :: 'a Tree) => flatten0 x) ps)"
    oops
end
