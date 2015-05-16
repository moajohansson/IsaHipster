theory tree_Flatten3
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  fun flatten3 :: "'a Tree => 'a list" where
  "flatten3 (Node (Node p x2 q) z r) =
     flatten3 (Node p x2 (Node q z r))"
  | "flatten3 (Node (Nil2) z r) = Cons2 z (flatten3 r)"
  | "flatten3 (Nil2) = Nil2"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (Cons2 y (Nil2))) (flatten0 q)"
  | "flatten0 (Nil2) = Nil2"
  hipster flatten3 append flatten0
  theorem x0 :
    "!! (p :: 'a Tree) . (flatten3 p) = (flatten0 p)"
    oops
end
