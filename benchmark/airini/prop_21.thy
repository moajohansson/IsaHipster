theory prop_21
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


hipster take leq len
lemma lemma_a [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_aa [thy_expl]: "take x1 NL.Nil = NL.Nil"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_ab [thy_expl]: "take x2 (take x2 y2) = take x2 y2"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_ac [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_ad [thy_expl]: "take (len x2) x2 = x2"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_ae [thy_expl]: "leq (S x2) x2 = False"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_af [thy_expl]: "take (len x16) (take y16 x16) = take y16 x16"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma lemma_ag [thy_expl]: "take (S x2) (take x2 y2) = take x2 y2"
by (hipster_induct_schemes take.simps Naturals.leq.simps len.simps)

lemma unknown [thy_expl]: "take x (take y z) = take y (take x z)"
oops

hipster_cond leq len take


theorem takeMore: "leq (len ts) n \<Longrightarrow> take n ts = ts"
by (hipster_induct_schemes leq.simps len.simps Nat.exhaust list.exhaust drop.simps)

end



