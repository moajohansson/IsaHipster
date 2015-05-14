theory tree_Flatten3
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  fun flatten3 :: "'a Tree => 'a list" where
  "flatten3 (Node (Node p x2 q) z r) =
     flatten3 (Node p x2 (Node q z r))"
  | "flatten3 (Node (Nil2) z r) = cons z (flatten3 r)"
  | "flatten3 (Nil2) = nil"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (cons y (nil))) (flatten0 q)"
  | "flatten0 (Nil2) = nil"
  theorem x0 :
    "!! (p :: 'a Tree) . (flatten3 p) = (flatten0 p)"
    oops
end
