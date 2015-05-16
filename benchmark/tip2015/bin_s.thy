theory bin_s
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"
  fun s :: "Bin => Bin" where
  "s (One) = ZeroAnd One"
  | "s (ZeroAnd xs) = OneAnd xs"
  | "s (OneAnd ys) = ZeroAnd (s ys)"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun toNat :: "Bin => Nat" where
  "toNat (One) = S Z"
  | "toNat (ZeroAnd xs) = plus (toNat xs) (toNat xs)"
  | "toNat (OneAnd ys) = S (plus (toNat ys) (toNat ys))"
  hipster s plus toNat
  theorem x0 :
    "!! (n :: Bin) . (toNat (s n)) = (S (toNat n))"
    oops
end
