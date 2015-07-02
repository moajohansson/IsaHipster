theory prop_12
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin


theorem initDef: "init (app ts (Cons t Nil)) = ts"
by hipster_induct_schemes


end



