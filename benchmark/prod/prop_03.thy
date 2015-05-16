theory prop_03
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  hipster plus length append
  theorem x0 :
    "!! (x :: 'a list) (y :: 'a list) .
       (length (append x y)) = (plus (length y) (length x))"
    oops
end
