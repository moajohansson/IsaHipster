theory prop_22
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem initAsTake: "init ts = take (sub (len ts) (S Z)) ts"
by (hipster_induct_schemes sub.simps Nat.exhaust)


end



