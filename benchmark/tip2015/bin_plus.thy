theory bin_plus
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"
  fun s :: "Bin => Bin" where
  "s (One) = ZeroAnd One"
  | "s (ZeroAnd xs) = OneAnd xs"
  | "s (OneAnd ys) = ZeroAnd (s ys)"
  fun plus2 :: "Bin => Bin => Bin" where
  "plus2 (One) y = s y"
  | "plus2 (ZeroAnd z) (One) = s (ZeroAnd z)"
  | "plus2 (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus2 z ys)"
  | "plus2 (ZeroAnd z) (OneAnd xs) = OneAnd (plus2 z xs)"
  | "plus2 (OneAnd x2) (One) = s (OneAnd x2)"
  | "plus2 (OneAnd x2) (ZeroAnd zs) = OneAnd (plus2 x2 zs)"
  | "plus2 (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus2 x2 ys2))"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun toNat :: "Bin => Nat" where
  "toNat (One) = S Z"
  | "toNat (ZeroAnd xs) = plus (toNat xs) (toNat xs)"
  | "toNat (OneAnd ys) = S (plus (toNat ys) (toNat ys))"
  hipster s plus2 plus toNat
  theorem x0 :
    "!! (x :: Bin) (y :: Bin) .
       (toNat (plus2 x y)) = (plus (toNat x) (toNat y))"
    oops
end
