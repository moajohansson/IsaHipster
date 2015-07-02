theory prop_18
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin


theorem notLen0: "leq (S n) (len ts) \<Longrightarrow> ts \<noteq> Nil" (* FIXME: loops in Hipster \<Longrightarrow> timeout on simp too? *)
by (metis len.simps(1) leq.simps(2))  (* XXX: maybe we do not add .simps rules to routine tacs? *)

end



