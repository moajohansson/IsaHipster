theory prop_11
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  hipster drop
  theorem x0 :
    "!! (xs :: 'a list) . (drop Z xs) = xs"
    oops
end
