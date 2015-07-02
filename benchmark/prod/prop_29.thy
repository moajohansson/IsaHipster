theory prop_29
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
  | "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster qrev append rev *)

(*hipster qrev append rev*)
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes qrev.simps append.simps rev.simps)

lemma lemma_aa [thy_expl]: "append (append x1 y1) z1 = append x1 (append y1 z1)"
by (hipster_induct_schemes qrev.simps append.simps rev.simps)

lemma lemma_ab [thy_expl]: "append (qrev x1 y1) z1 = qrev x1 (append y1 z1)"
by (hipster_induct_schemes qrev.simps append.simps rev.simps)

lemma lemma_ac [thy_expl]: "qrev (append x1 y1) z1 = qrev y1 (qrev x1 z1)"
by (hipster_induct_schemes qrev.simps append.simps rev.simps)

lemma lemma_ad [thy_expl]: "qrev (qrev x1 y1) z1 = qrev y1 (append x1 z1)"
by (hipster_induct_schemes qrev.simps append.simps rev.simps)

lemma lemma_ae [thy_expl]: "append (rev x3) y3 = qrev x3 y3"
by (hipster_induct_schemes qrev.simps append.simps rev.simps)

  theorem x0 :
    "(rev (qrev x (Nil2))) = x"
    by (hipster_induct_schemes qrev.simps append.simps rev.simps)
end
