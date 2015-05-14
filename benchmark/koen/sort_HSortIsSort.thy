theory sort_HSortIsSort
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Heap = Node "'a Heap" "'a" "'a Heap" | Nil2
  fun toHeap2 :: "int list => (int Heap) list" where
  "toHeap2 (nil) = nil"
  | "toHeap2 (cons y z) = cons (Node (Nil2) y (Nil2)) (toHeap2 z)"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun hmerge :: "int Heap => int Heap => int Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
     (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
        Node (hmerge (Node z x2 x3) x6) x5 x4)"
  | "hmerge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "hmerge (Nil2) y = y"
  fun hpairwise :: "(int Heap) list => (int Heap) list" where
  "hpairwise (nil) = nil"
  | "hpairwise (cons p (nil)) = cons p (nil)"
  | "hpairwise (cons p (cons q qs)) =
       cons (hmerge p q) (hpairwise qs)"
  fun hmerging :: "(int Heap) list => int Heap" where
  "hmerging (nil) = Nil2"
  | "hmerging (cons p (nil)) = p"
  | "hmerging (cons p (cons z x2)) =
       hmerging (hpairwise (cons p (cons z x2)))"
  fun toHeap :: "int list => int Heap" where
  "toHeap x = hmerging (toHeap2 x)"
  fun toList :: "int Heap => int list" where
  "toList (Node p y q) = cons y (toList (hmerge p q))"
  | "toList (Nil2) = nil"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun hsort :: "int list => int list" where
  "hsort x =
     dot
       (% (y :: int Heap) => toList y) (% (z :: int list) => toHeap z) x"
  theorem x0 :
    "!! (x :: int list) . (hsort x) = (isort x)"
    oops
end
