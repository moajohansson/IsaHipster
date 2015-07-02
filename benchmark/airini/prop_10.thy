theory prop_10
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin



theorem unknown02 : "init (tail x) = tail (init x)"
by hipster_induct_schemes

end



