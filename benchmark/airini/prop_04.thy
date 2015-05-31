theory prop_04
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin

hipster last app
lemma lemma_a [thy_expl]: "app x2 NL.Nil = x2"
by (hipster_induct_schemes Listi.last.simps Listi.app.simps)

lemma lemma_aa [thy_expl]: "app (app x1 y1) z1 = app x1 (app y1 z1)"
by (hipster_induct_schemes Listi.last.simps Listi.app.simps)

lemma unknown [thy_expl]: "Listi.last (app x x) = Listi.last x"
oops

theorem lastApp: "notNil ts \<Longrightarrow> last (app rs ts) = last ts"
by (hipster_induct_schemes last.simps app.simps notNil.simps NL.exhaust)


end


