theory lezpAdd

imports Main
        "../nats"
(* NB: just testing. Realised Isabelle imports the first theory module with a matching name,
      regardless of the theory name. However, to be checked: happened at exploration and the
      theory being imported was merely "../Naturals" :w *)

begin

(*hipster lezp add*)
lemma lemma_a [thy_expl]: "add x2 Z = x2"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_aa [thy_expl]: "add (add x2 y2) z2 = add x2 (add y2 z2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ab [thy_expl]: "add x2 (S y2) = S (add x2 y2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ac [thy_expl]: "add x2 (add y2 x2) = add y2 (add x2 x2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ad [thy_expl]: "add x2 (add y2 y2) = add y2 (add y2 x2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ae [thy_expl]: "add x2 (S y2) = S (add y2 x2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_af [thy_expl]: "add (S x2) y2 = S (add y2 x2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ag [thy_expl]: "lezp (add x2 x2) = lezp x2"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ah [thy_expl]: "add (add x2 y2) (add x2 z2) = add (add x2 z2) (add x2 y2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ai [thy_expl]: "add (add x2 y2) (add z2 x2) = add (add z2 x2) (add x2 y2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_aj [thy_expl]: "add (add x3 y3) (add z3 y3) = add (add z3 x3) (add y3 y3)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ak [thy_expl]: "add (add x3 y3) (S z3) = add (add z3 x3) (S y3)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_al [thy_expl]: "add (add x3 x3) (add y3 z3) = add (add x3 y3) (add x3 z3)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_am [thy_expl]: "add (S x2) (add y2 z2) = add (add y2 x2) (S z2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_an [thy_expl]: "add (S x2) (add y2 z2) = add (add y2 z2) (S x2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ao [thy_expl]: "add (S x2) (S y2) = add (S y2) (S x2)"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_ap [thy_expl]: "lezp y3 \<Longrightarrow> add x3 y3 = x3"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

lemma lemma_aq [thy_expl]: "add x2 y2 = add y2 x2"
by (hipster_induct_schemes nats.lezp.simps nats.add.simps)

end
