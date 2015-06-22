theory prop_28
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  fun qrevflat :: "('a list) list => 'a list => 'a list" where
  "qrevflat (Nil2) y = y"
  | "qrevflat (Cons2 xs xss) y = qrevflat xss (append (rev xs) y)"
  fun revflat :: "('a list) list => 'a list" where
  "revflat (Nil2) = Nil2"
  | "revflat (Cons2 xs xss) = append (revflat xss) (rev xs)"
  (*hipster append rev qrevflat revflat *)

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes  append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes append.simps)

lemma lemma_ab [thy_expl]: "append (rev x4) (rev y4) = rev (append y4 x4)"
by (hipster_induct_schemes rev.simps append.simps)

lemma lemma_ac [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes rev.simps append.simps)

hipster qrevflat revflat append rev
lemma lemma_ad [thy_expl]: "append (qrevflat x3 y3) z3 = qrevflat x3 (append y3 z3)"
by (hipster_induct_schemes qrevflat.simps revflat.simps append.simps)

lemma lemma_ae [thy_expl]: "qrevflat x3 Nil2 = revflat x3"
by (hipster_induct_schemes qrevflat.simps revflat.simps append.simps rev.simps)

  theorem x0 :
    "(revflat x) = (qrevflat x (Nil2))"
    by (hipster_induct_schemes qrevflat.simps revflat.simps append.simps)

    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
