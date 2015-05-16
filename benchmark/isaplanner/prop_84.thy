theory prop_84
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
  | "zip (Cons2 z x2) (Nil2) = Nil2"
  | "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip x2 x4)"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster zip take len drop append *)
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'a1 list) (zs :: 'a1 list) .
       (zip xs (append ys zs)) =
         (append (zip (take (len ys) xs) ys) (zip (drop (len ys) xs) zs))"
    by (hipster_induct_schemes)
end
