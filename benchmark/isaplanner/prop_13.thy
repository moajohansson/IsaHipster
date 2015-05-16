theory prop_13
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  hipster drop
  theorem x0 :
    "!! (n :: Nat) (x :: 'a) (xs :: 'a list) .
       (drop (S n) (Cons2 x xs)) = (drop n xs)"
    oops
end
