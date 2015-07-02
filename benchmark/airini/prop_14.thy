theory prop_14
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin


theorem count03: "count t ts = n \<Longrightarrow> count t (app rs ts) = add (count t rs) n"
by (hipster_induct_simp_metis)


end



