theory prop_58
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = nil2"
  | "zip (Cons2 z x2) (Nil2) = nil2"
  | "zip (Cons2 z x2) (cons2 x3 x4) = cons2 (Pair z x3) (zip x2 x4)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  hipster zip drop
  theorem x0 :
    "!! (n :: Nat) (xs :: 'a list) (ys :: 'b list) .
       (drop n (zip xs ys)) = (zip (drop n xs) (drop n ys))"
    oops
end
