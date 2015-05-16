theory prop_42
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = nil2"
  | "take (S z) (Cons2 x2 x3) = cons2 x2 (take z x3)"
  hipster take
  theorem x0 :
    "!! (n :: Nat) (x :: 'a) (xs :: 'a list) .
       (take (S n) (Cons2 x xs)) = (cons2 x (take n xs))"
    oops
end
