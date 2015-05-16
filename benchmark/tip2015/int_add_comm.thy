theory int_add_comm
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Zero | Succ "Nat"
  datatype Z = P "Nat" | N "Nat"
  fun plus2 :: "Nat => Nat => Nat" where
  "plus2 (Zero) y = y"
  | "plus2 (Succ n) y = Succ (plus2 n y)"
  fun minus :: "Nat => Nat => Z" where
  "minus (Zero) (Zero) = P Zero"
  | "minus (Zero) (Succ n) = N n"
  | "minus (Succ m) (Zero) = P (Succ m)"
  | "minus (Succ m) (Succ o) = minus m o"
  fun plus :: "Z => Z => Z" where
  "plus (P m) (P n) = P (plus2 m n)"
  | "plus (P m) (N o) = minus m (Succ o)"
  | "plus (N m2) (P n2) = minus n2 (Succ m2)"
  | "plus (N m2) (N n3) = N (Succ (plus2 m2 n3))"
  hipster plus2 minus plus
  theorem x0 :
    "!! (x :: Z) (y :: Z) . (plus x y) = (plus y x)"
    oops
end
