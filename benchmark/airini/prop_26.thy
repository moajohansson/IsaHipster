theory prop_26
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem countIns0: "\<not> eqN r t \<Longrightarrow> count t ts = count t (insert r ts)"
by hipster_induct_schemes



end



