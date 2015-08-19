theory prop_41
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
  fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (Nil2) y = Nil2"
  | "intersect (Cons2 z xs) y =
       (if elem z y then Cons2 z (intersect xs y) else intersect xs y)"
  fun subset :: "Nat list => Nat list => bool" where
  "subset (Nil2) y = True"
  | "subset (Cons2 z xs) y =
       (if elem z y then subset xs y else False)"
  (*hipster equal2 elem intersect subset *)

  theorem x0 :
    "(subset x y) ==> ((intersect x y) = x)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end