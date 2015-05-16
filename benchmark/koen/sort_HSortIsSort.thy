theory sort_HSortIsSort
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Heap = Node "'a Heap" "'a" "'a Heap" | Nil2
  fun toHeap2 :: "int list => (int Heap) list" where
  "toHeap2 (Nil2) = nil2"
  | "toHeap2 (Cons2 y z) = cons2 (Node (Nil2) y (Nil2)) (toHeap2 z)"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (cons2 z xs) else cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun hmerge :: "int Heap => int Heap => int Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
     (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
        Node (hmerge (Node z x2 x3) x6) x5 x4)"
  | "hmerge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "hmerge (Nil2) y = y"
  fun hpairwise :: "(int Heap) list => (int Heap) list" where
  "hpairwise (Nil2) = nil2"
  | "hpairwise (Cons2 p (Nil2)) = cons2 p (nil2)"
  | "hpairwise (Cons2 p (cons2 q qs)) =
       Cons2 (hmerge p q) (hpairwise qs)"
  fun hmerging :: "(int Heap) list => int Heap" where
  "hmerging (Nil2) = Nil2"
  | "hmerging (Cons2 p (Nil2)) = p"
  | "hmerging (Cons2 p (cons2 z x2)) =
       hmerging (hpairwise (Cons2 p (cons2 z x2)))"
  fun toHeap :: "int list => int Heap" where
  "toHeap x = hmerging (toHeap2 x)"
  fun toList :: "int Heap => int list" where
  "toList (Node p y q) = Cons2 y (toList (hmerge p q))"
  | "toList (Nil2) = Nil2"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun hsort :: "int list => int list" where
  "hsort x =
     dot
       (% (y :: int Heap) => toList y) (% (z :: int list) => toHeap z) x"
  hipster toHeap2
          insert2
          isort
          hmerge
          hpairwise
          hmerging
          toHeap
          toList
          dot
          hsort
  theorem x0 :
    "!! (x :: int list) . (hsort x) = (isort x)"
    oops
end
