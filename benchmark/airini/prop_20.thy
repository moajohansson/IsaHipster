theory prop_20
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem emptyDrop: "leq (len ts) n \<Longrightarrow> drop n ts = Nil"
by (hipster_induct_schemes noLowerZ len0  leq.simps len.simps) 

end



