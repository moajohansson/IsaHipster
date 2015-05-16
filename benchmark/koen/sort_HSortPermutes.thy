theory sort_HSortPermutes
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  datatype 'a Heap = Node "'a Heap" "'a" "'a Heap" | Nil2
  fun toHeap2 :: "int list => (int Heap) list" where
  "toHeap2 (Nil2) = nil2"
  | "toHeap2 (Cons2 y z) = cons2 (Node (Nil2) y (Nil2)) (toHeap2 z)"
  fun hmerge :: "int Heap => int Heap => int Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
     (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
        Node (hmerge (Node z x2 x3) x6) x5 x4)"
  | "hmerge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "hmerge (Nil2) y = y"
  fun hpairwise :: "(int Heap) list => (int Heap) list" where
  "hpairwise (Nil2) = nil2"
  | "hpairwise (Cons2 q (Nil2)) = cons2 q (nil2)"
  | "hpairwise (Cons2 q (cons2 q2 qs)) =
       Cons2 (hmerge q q2) (hpairwise qs)"
  fun hmerging :: "(int Heap) list => int Heap" where
  "hmerging (Nil2) = Nil2"
  | "hmerging (Cons2 q (Nil2)) = q"
  | "hmerging (Cons2 q (cons2 z x2)) =
       hmerging (hpairwise (Cons2 q (cons2 z x2)))"
  fun toHeap :: "int list => int Heap" where
  "toHeap x = hmerging (toHeap2 x)"
  fun toList :: "int Heap => int list" where
  "toList (Node q y q2) = Cons2 y (toList (hmerge q q2))"
  | "toList (Nil2) = Nil2"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun hsort :: "int list => int list" where
  "hsort x =
     dot
       (% (y :: int Heap) => toList y) (% (z :: int list) => toHeap z) x"
  fun count :: "int => int list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z xs) =
       (if x = z then S (count x xs) else count x xs)"
  hipster toHeap2
          hmerge
          hpairwise
          hmerging
          toHeap
          toList
          dot
          hsort
          count
  theorem x0 :
    "!! (x :: int) (y :: int list) . (count x (hsort y)) = (count x y)"
    oops
end
