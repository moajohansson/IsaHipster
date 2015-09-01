theory prop_11

imports Main
        "$HIPSTER_HOME/IsaHipster"

begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"
fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
| "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"


hipster append rev


  theorem revAppend :
    "(rev (append (rev x) (rev y))) = (append y x)"
    by (hipster_induct_schemes append.simps rev.simps)




(*    by (hipster_induct_schemes rev.simps append.simps)*)




(*
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes append.simps rev.simps list.exhaust)

lemma lemma_aa [thy_expl]: "append (append x1 y1) z1 =
append x1 (append y1 z1)"
by (hipster_induct_schemes append.simps rev.simps list.exhaust)

lemma lemma_ab [thy_expl]: "append (rev x4) (rev y4) =
rev (append y4 x4)"
by (hipster_induct_schemes append.simps rev.simps list.exhaust)

lemma lemma_ac [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes append.simps rev.simps list.exhaust)
*)

(*by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)

end

