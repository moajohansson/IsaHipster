theory prop_84
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (nil) y = nil"
  | "zip (cons z x2) (nil) = nil"
  | "zip (cons z x2) (cons x3 x4) = cons (Pair z x3) (zip x2 x4)"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil"
  | "take (S z) (nil) = nil"
  | "take (S z) (cons x2 x3) = cons x2 (take z x3)"
  fun len :: "'a list => Nat" where
  "len (nil) = Z"
  | "len (cons y xs) = S (len xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  hipster zip take len drop append
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'a1 list) (zs :: 'a1 list) .
       (zip xs (append ys zs)) =
         (append (zip (take (len ys) xs) ys) (zip (drop (len ys) xs) zs))"
    oops
end
