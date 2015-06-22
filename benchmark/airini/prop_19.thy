theory prop_19
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem notEmptyDrop: "leq (S n) (len ts) \<Longrightarrow> (drop n ts) \<noteq> Nil"
by (hipster_induct_schemes leq.simps len.simps)

end



