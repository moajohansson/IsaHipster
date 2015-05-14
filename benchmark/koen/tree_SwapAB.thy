theory tree_SwapAB
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  fun swap :: "int => int => int Tree => int Tree" where
  "swap x y (Node p x2 q) =
     (if x2 = x then Node (swap x y p) y (swap x y q) else
        (if x2 = y then Node (swap x y p) x (swap x y q) else
           Node (swap x y p) x2 (swap x y q)))"
  | "swap x y (Nil2) = Nil2"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun elem :: "int => int list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (x = z) (elem x ys)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun flatten0 :: "'a Tree => 'a list" where
  "flatten0 (Node p y q) =
     append (append (flatten0 p) (cons y (nil))) (flatten0 q)"
  | "flatten0 (Nil2) = nil"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  theorem x0 :
    "!! (p :: int Tree) (a :: int) (b :: int) .
       (and2 (elem a (flatten0 p)) (elem b (flatten0 p))) ==>
         (and2
            (elem a (flatten0 (swap a b p))) (elem b (flatten0 (swap a b p))))"
    oops
end
