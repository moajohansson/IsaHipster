theory list_PairUnpair
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun unpair :: "(('t, 't) Pair2) list => 't list" where
  "unpair (nil) = nil"
  | "unpair (cons (Pair z y2) xys) = cons z (cons y2 (unpair xys))"
  fun pairs :: "'t list => (('t, 't) Pair2) list" where
  "pairs (nil) = nil"
  | "pairs (cons y (nil)) = nil"
  | "pairs (cons y (cons y2 xs)) = cons (Pair y y2) (pairs xs)"
  fun length :: "'t list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  fun even :: "Nat => bool" where
  "even (Z) = True"
  | "even (S (Z)) = False"
  | "even (S (S z)) = even z"
  theorem x0 :
    "!! (xs :: 't list) .
       (even (length xs)) ==> ((unpair (pairs xs)) = xs)"
    oops
end
