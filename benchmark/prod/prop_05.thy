theory prop_05
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster length append rev *)

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes length.simps append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 =
append x2 (append y2 z2)"
by (hipster_induct_schemes length.simps append.simps)

(*hipster rev append*)
lemma lemma_ab [thy_expl]: "append (rev x5) (rev y5) = rev (append y5 x5)"
by (hipster_induct_schemes rev.simps append.simps)

lemma lemma_ac [thy_expl]: "rev (rev x5) = x5"
by (hipster_induct_schemes rev.simps append.simps)
(*
lemma ax: "length (append (Cons2 ya xs) y) = S (length (append xs y))"
by (metis length.simps(2) append.simps(2))
*)

lemma ax2[thy_expl]: "length (append y (Cons2 ya xs)) = S (length (append y xs))"
by(hipster_induct_schemes)

hipster length rev append
lemma unknown []: "length (append x y) = length (append y x)"
oops

lemma unknown []: "length (rev x) = length x"
oops

  theorem x0 :
    "(length (rev x)) = (length x)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
