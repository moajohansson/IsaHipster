theory prop_20
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem emptyDrop: "leq (len ts) n \<Longrightarrow> drop n ts = Nil"
by (hipster_induct_schemes Nat.exhaust list.exhaust drop.simps leq.simps len.simps) 

end



