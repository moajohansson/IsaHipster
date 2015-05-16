theory prop_16
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  (*hipster last *)
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) .
       (xs = (Nil2)) ==> ((last (Cons2 x xs)) = x)"
    by (hipster_induct_schemes)
end
