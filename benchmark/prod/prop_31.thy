theory prop_31
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
  | "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"
  (*hipster qrev *)

lemma lemma_a [thy_expl]: "qrev (qrev x2 y2) Nil2 = qrev y2 x2"
by (hipster_induct_schemes qrev.simps)

  theorem x0 :
    "(qrev (qrev x (Nil2)) (Nil2)) = x"
    by (hipster_induct_schemes qrev.simps)
end
