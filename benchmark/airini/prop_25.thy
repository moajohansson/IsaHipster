theory prop_25
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem countIns: "S (count t ts) = count t (insert t ts)"
by hipster_induct_simp_metis



end



