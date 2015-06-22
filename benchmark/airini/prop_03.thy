theory prop_03
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin

theorem initAppNil: "\<not> notNil ts \<Longrightarrow> init (app rs ts) = init rs"
by (hipster_induct_schemes notNil.simps app.simps init.simps NL.exhaust)


end


