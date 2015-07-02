theory prop_01
imports Main
        "../../TestTheories/Listing"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin


theorem initLast: "ts \<noteq> Nil \<Longrightarrow> app (init ts) (Cons (last ts) Nil) = ts"
by (hipster_induct_schemes)

end


