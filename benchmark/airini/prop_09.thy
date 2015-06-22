theory prop_09
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem initMaps : "init (maps x y) = maps x (init y)"
by hipster_induct_schemes

end



