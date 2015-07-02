theory prop_11
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin



theorem unknown03 : "len (init x) = len (tail x)"
by hipster_induct_schemes

end



