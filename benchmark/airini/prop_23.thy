theory prop_23
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem zipNotNil: "notNil rs \<Longrightarrow> zip (Cons t ts) rs = Cons (t, head rs) (zip ts (tail rs))"
by hipster_induct_simp_metis 


end



