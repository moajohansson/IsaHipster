theory list_PairUnpair
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun unpair :: "(('t, 't) Pair2) list => 't list" where
  "unpair (Nil2) = nil2"
  | "unpair (Cons2 (Pair z y2) xys) =
       Cons2 z (cons2 y2 (unpair xys))"
  fun pairs :: "'t list => (('t, 't) Pair2) list" where
  "pairs (Nil2) = nil2"
  | "pairs (Cons2 y (Nil2)) = nil2"
  | "pairs (Cons2 y (cons2 y2 xs)) = cons2 (Pair y y2) (pairs xs)"
  fun length :: "'t list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun even :: "Nat => bool" where
  "even (Z) = True"
  | "even (S (Z)) = False"
  | "even (S (S z)) = even z"
  hipster unpair pairs length even
  theorem x0 :
    "!! (xs :: 't list) .
       (even (length xs)) ==> ((unpair (pairs xs)) = xs)"
    oops
end
