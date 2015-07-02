theory prop_08
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin

theorem lemma_a [thy_expl]: "tail (maps x2 y2) = maps x2 (tail y2)"
by hipster_induct_schemes


end


