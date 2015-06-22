theory prop_17
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem lenTake: "leq n (len ts) \<Longrightarrow> len (take n ts) = n" (* XXX: same as previous *)
by hipster_induct_schemes

end



