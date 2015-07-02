theory prop_40
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  fun subset :: "Nat list => Nat list => bool" where
  "subset (Nil2) y = True"
  | "subset (Cons2 z xs) y =
       (if elem z y then subset xs y else False)"
  fun union :: "Nat list => Nat list => Nat list" where
  "union (Nil2) y = y"
  | "union (Cons2 z xs) y =
       (if elem z y then union xs y else Cons2 z (union xs y))"
  (*hipster equal2 elem subset union *)
(*
hipster_cond subset union
*)
  theorem x0 :
    "(subset x y) ==> ((union x y) = y)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
