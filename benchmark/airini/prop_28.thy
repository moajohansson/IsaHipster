theory prop_28
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin

hipster rev app
lemma lemma_a [thy_expl]: "app x2 NL.Nil = x2"
by (hipster_induct_schemes Listi.rev.simps Listi.app.simps)

lemma lemma_aa [thy_expl]: "app (app x1 y1) z1 = app x1 (app y1 z1)"
by (hipster_induct_schemes Listi.rev.simps Listi.app.simps)

lemma lemma_ab [thy_expl]: "app (Listi.rev x9) (Listi.rev y9) = Listi.rev (app y9 x9)"
by (hipster_induct_schemes Listi.rev.simps Listi.app.simps)

lemma lemma_ac [thy_expl]: "Listi.rev (Listi.rev x8) = x8"
by (hipster_induct_schemes Listi.rev.simps Listi.app.simps)

theorem palyn : "t = rev t \<Longrightarrow> rev (app t t) = app t t"
by (hipster_induct_schemes rev.simps app.simps)

end



