theory heap_merge
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  datatype Heap = Node "Heap" "Nat" "Heap" | Nil2
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun merge :: "Heap => Heap => Heap" where
  "merge (Node z x2 x3) (Node x4 x5 x6) =
     (if le x2 x5 then Node (merge x3 (Node x4 x5 x6)) x2 z else
        Node (merge (Node z x2 x3) x6) x5 x4)"
  | "merge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "merge (Nil2) y = y"
  fun toList :: "Nat => Heap => Nat list" where
  "toList (Z) y = Nil2"
  | "toList (S z) (Node x2 x3 x4) =
       Cons2 x3 (toList z (merge x2 x4))"
  | "toList (S z) (Nil2) = Nil2"
  fun mergeLists :: "Nat list => Nat list => Nat list" where
  "mergeLists (Nil2) y = y"
  | "mergeLists (Cons2 z x2) (Nil2) = Cons2 z x2"
  | "mergeLists (Cons2 z x2) (Cons2 x3 x4) =
       (if le z x3 then Cons2 z (mergeLists x2 (Cons2 x3 x4)) else
          Cons2 x3 (mergeLists (Cons2 z x2) x4))"
  fun heapSize :: "Heap => Nat" where
  "heapSize (Node l y r) = S (plus (heapSize l) (heapSize r))"
  | "heapSize (Nil2) = Z"
  fun toList2 :: "Heap => Nat list" where
  "toList2 x = toList (heapSize x) x"
  (*hipster plus le merge toList mergeLists heapSize toList2 *)
  theorem x0 :
    "(toList2 (merge x y)) = (mergeLists (toList2 x) (toList2 y))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
