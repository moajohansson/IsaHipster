theory sort_HSortPermutes
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  datatype 'a Heap = Node "'a Heap" "'a" "'a Heap" | Nil2
  fun toHeap2 :: "int list => (int Heap) list" where
  "toHeap2 (nil) = nil"
  | "toHeap2 (cons y z) = cons (Node (Nil2) y (Nil2)) (toHeap2 z)"
  fun hmerge :: "int Heap => int Heap => int Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
     (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
        Node (hmerge (Node z x2 x3) x6) x5 x4)"
  | "hmerge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "hmerge (Nil2) y = y"
  fun hpairwise :: "(int Heap) list => (int Heap) list" where
  "hpairwise (nil) = nil"
  | "hpairwise (cons q (nil)) = cons q (nil)"
  | "hpairwise (cons q (cons q2 qs)) =
       cons (hmerge q q2) (hpairwise qs)"
  fun hmerging :: "(int Heap) list => int Heap" where
  "hmerging (nil) = Nil2"
  | "hmerging (cons q (nil)) = q"
  | "hmerging (cons q (cons z x2)) =
       hmerging (hpairwise (cons q (cons z x2)))"
  fun toHeap :: "int list => int Heap" where
  "toHeap x = hmerging (toHeap2 x)"
  fun toList :: "int Heap => int list" where
  "toList (Node q y q2) = cons y (toList (hmerge q q2))"
  | "toList (Nil2) = nil"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun hsort :: "int list => int list" where
  "hsort x =
     dot
       (% (y :: int Heap) => toList y) (% (z :: int list) => toHeap z) x"
  fun count :: "int => int list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z xs) =
       (if x = z then S (count x xs) else count x xs)"
  theorem x0 :
    "!! (x :: int) (y :: int list) . (count x (hsort y)) = (count x y)"
    oops
end
