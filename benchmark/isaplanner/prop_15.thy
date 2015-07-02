theory prop_15
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun ins :: "Nat => Nat list => Nat list" where
  "ins x (Nil2) = Cons2 x (Nil2)"
  | "ins x (Cons2 z xs) =
       (if lt x z then Cons2 x (Cons2 z xs) else Cons2 z (ins x xs))"
  (*hipster lt len ins *)
  theorem x0 :
    "(len (ins x xs)) = (S (len xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
