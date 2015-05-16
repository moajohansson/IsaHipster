theory sort_HSortSorts
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Heap = Node "'a Heap" "'a" "'a Heap" | Nil2
  fun toHeap2 :: "int list => (int Heap) list" where
  "toHeap2 (Nil2) = Nil2"
  | "toHeap2 (Cons2 y z) = Cons2 (Node (Nil2) y (Nil2)) (toHeap2 z)"
  fun hmerge :: "int Heap => int Heap => int Heap" where
  "hmerge (Node z x2 x3) (Node x4 x5 x6) =
     (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
        Node (hmerge (Node z x2 x3) x6) x5 x4)"
  | "hmerge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "hmerge (Nil2) y = y"
  fun hpairwise :: "(int Heap) list => (int Heap) list" where
  "hpairwise (Nil2) = Nil2"
  | "hpairwise (Cons2 p (Nil2)) = Cons2 p (Nil2)"
  | "hpairwise (Cons2 p (Cons2 q qs)) =
       Cons2 (hmerge p q) (hpairwise qs)"
  fun hmerging :: "(int Heap) list => int Heap" where
  "hmerging (Nil2) = Nil2"
  | "hmerging (Cons2 p (Nil2)) = p"
  | "hmerging (Cons2 p (Cons2 z x2)) =
       hmerging (hpairwise (Cons2 p (Cons2 z x2)))"
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
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (Nil2) = True"
  | "ordered (Cons2 y (Nil2)) = True"
  | "ordered (Cons2 y (Cons2 y2 xs)) =
       and2 (y <= y2) (ordered (Cons2 y2 xs))"
  hipster toHeap2
          hmerge
          hpairwise
          hmerging
          toHeap
          toList
          dot
          hsort
          and2
          ordered
  theorem x0 :
    "!! (x :: int list) . ordered (hsort x)"
    oops
end
