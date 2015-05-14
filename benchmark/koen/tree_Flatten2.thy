theory tree_Flatten2
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  fun flatten2 :: "'a Tree => 'a list => 'a list" where
  "flatten2 (Node p z q) y = flatten2 p (cons z (flatten2 q y))"
  | "flatten2 (Nil2) y = y"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (cons y (nil))) (flatten0 q)"
  | "flatten0 (Nil2) = nil"
  theorem x0 :
    "!! (p :: 'a Tree) . (flatten2 p (nil)) = (flatten0 p)"
    oops
end
