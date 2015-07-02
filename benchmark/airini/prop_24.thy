theory prop_24
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin


theorem elemCount: "elem t ts \<Longrightarrow> lt Z (count t ts)"
by hipster_induct_simp_metis


end



