theory tree_Flatten1
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
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (cons y (nil))) (flatten0 q)"
  | "flatten0 (Nil2) = nil"
  theorem x0 :
    "!! (p :: 'a Tree) . (flatten1 (cons p (nil))) = (flatten0 p)"
    oops
end
