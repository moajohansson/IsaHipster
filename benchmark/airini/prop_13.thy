theory prop_13
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin

hipster eqN
lemma lemma_a [thy_expl]: "eqN x2 y2 = eqN y2 x2"
by (hipster_induct_schemes eqN.simps)

lemma lemma_aa [thy_expl]: "eqN x2 x2 = True"
by (hipster_induct_schemes eqN.simps)

lemma lemma_ab [thy_expl]: "eqN x2 (S x2) = False"
by (hipster_induct_schemes eqN.simps)

theorem count02: "count t ts = n \<Longrightarrow> count t (Cons t ts) = S n"
by (hipster_induct_schemes)

end



