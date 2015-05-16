theory nicomachus_theorem
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun sum :: "Nat => Nat" where
  "sum (Z) = Z"
  | "sum (S n) = plus (sum n) (S n)"
  fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
  | "mult (S n) y = plus y (mult n y)"
  fun cubes :: "Nat => Nat" where
  "cubes (Z) = Z"
  | "cubes (S n) = plus (cubes n) (mult (mult (S n) (S n)) (S n))"
  hipster plus sum mult cubes
  theorem x0 :
    "!! (n :: Nat) . (cubes n) = (mult (sum n) (sum n))"
    oops
end
