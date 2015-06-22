theory prop_02
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin

(*hipster init app*)
lemma lemma_a [thy_expl]: "app x2 Nil = x2"
by (hipster_induct_schemes init.simps app.simps)

lemma lemma_aa [thy_expl]: "app (app x1 y1) z1 = app x1 (app y1 z1)"
by (hipster_induct_schemes init.simps app.simps)

lemma unknown [thy_expl]: "init (app x x) = app x (init x)"
oops

(*
hipster_cond notNil init*)

theorem initApp: "notNil ts \<Longrightarrow> init (app rs ts) = app rs (init ts)"
by (hipster_induct_schemes notNil.simps init.simps app.simps NL.exhaust)

end


