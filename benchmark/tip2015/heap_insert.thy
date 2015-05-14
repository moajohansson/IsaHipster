theory heap_insert
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  datatype Heap = Node "Heap" "Nat" "Heap" | Nil2
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun listInsert :: "Nat => Nat list => Nat list" where
  "listInsert x (nil) = cons x (nil)"
  | "listInsert x (cons z ys) =
       (if le x z then cons x (cons z ys) else cons z (listInsert x ys))"
  fun merge :: "Heap => Heap => Heap" where
  "merge (Node z x2 x3) (Node x4 x5 x6) =
     (if le x2 x5 then Node (merge x3 (Node x4 x5 x6)) x2 z else
        Node (merge (Node z x2 x3) x6) x5 x4)"
  | "merge (Node z x2 x3) (Nil2) = Node z x2 x3"
  | "merge (Nil2) y = y"
  fun toList :: "Nat => Heap => Nat list" where
  "toList (Z) y = nil"
  | "toList (S z) (Node x2 x3 x4) = cons x3 (toList z (merge x2 x4))"
  | "toList (S z) (Nil2) = nil"
  fun insert2 :: "Nat => Heap => Heap" where
  "insert2 x y = merge (Node Nil2 x Nil2) y"
  fun heapSize :: "Heap => Nat" where
  "heapSize (Node l y r) = S (plus (heapSize l) (heapSize r))"
  | "heapSize (Nil2) = Z"
  fun toList2 :: "Heap => Nat list" where
  "toList2 x = toList (heapSize x) x"
  theorem x0 :
    "!! (x :: Nat) (h :: Heap) .
       (toList2 (insert2 x h)) = (listInsert x (toList2 h))"
    oops
end
