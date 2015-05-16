theory prop_32
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
  | "rotate (S z) (Nil2) = nil2"
  | "rotate (S z) (Cons2 x2 x3) =
       rotate z (append x3 (Cons2 x2 (Nil2)))"
  hipster length append rotate
  theorem x0 :
    "!! (x :: 'a list) . (rotate (length x) x) = x"
    oops
end
