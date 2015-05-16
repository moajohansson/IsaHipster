theory prop_04
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun double :: "Nat => Nat" where
  "double (Z) = Z"
  | "double (S y) = S (S (double y))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  hipster length double append
  theorem x0 :
    "!! (x :: 'a list) . (length (append x x)) = (double (length x))"
    oops
end
