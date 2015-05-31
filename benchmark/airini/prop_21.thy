theory prop_21
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem takeMore: "leq (len ts) n \<Longrightarrow> take n ts = ts"
by (hipster_induct_schemes emptyDrop drop.simps)

end



