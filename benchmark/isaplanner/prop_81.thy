theory prop_81
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil"
  | "take (S z) (nil) = nil"
  | "take (S z) (cons x2 x3) = cons x2 (take z x3)"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  hipster take plus drop
  theorem x0 :
    "!! (n :: Nat) (m :: Nat) (xs :: 'a list) .
       (take n (drop m xs)) = (drop m (take (plus n m) xs))"
    oops
end
