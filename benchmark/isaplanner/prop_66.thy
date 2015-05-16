theory prop_66
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter x (Nil2) = nil2"
  | "filter x (Cons2 z xs) =
       (if x z then Cons2 z (filter x xs) else filter x xs)"
  hipster len le filter
  theorem x0 :
    "!! (q :: ('a => bool)) (xs :: 'a list) .
       le (len (filter q xs)) (len xs)"
    oops
end
