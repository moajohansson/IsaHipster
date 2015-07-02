theory prop_60
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun null2 :: "Nat list => bool" where
  "null2 (Nil2) = True"
  | "null2 (Cons2 y z) = False"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  fun append :: "Nat list => Nat list => Nat list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster null last append *)
(*hipster last null2 append*)(*
lemma lemma_a []: "append x2 Nil2 = x2"
by (hipster_induct_schemes last.simps null2.simps append.simps)

lemma lemma_aa []: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes last.simps null2.simps append.simps)

lemma lemma_ab []: "null2 (append x2 x2) = null2 x2"
by (hipster_induct_schemes last.simps null2.simps append.simps)

(*hipster null2 append*)
lemma unknown []: "null2 (append x y) = null2 (append y x)"
by (hipster_induct_schemes last.simps null2.simps append.simps list.exhaust)

(*hipster_cond null2 append*)
lemma lemma_ac []: "null2 x2 \<Longrightarrow> append x2 y2 = y2"
by (hipster_induct_schemes null2.simps append.simps)*)

  theorem x0 :
    "(~ (null2 ys)) ==> ((last (append xs ys)) = (last ys))"
    by (hipster_induct_schemes last.simps null2.simps append.simps list.exhaust) (*
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
