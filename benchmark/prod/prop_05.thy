theory prop_05
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
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = nil2"
  | "rev (Cons2 y xs) = append (rev xs) (cons2 y (Nil2))"
  hipster length append rev
  theorem x0 :
    "!! (x :: 'a list) . (length (rev x)) = (length x)"
    oops
end
