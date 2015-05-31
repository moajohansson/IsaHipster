theory prop_15
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin

hipster rev app elem
lemma lemma_a [thy_expl]: "eqN x2 y2 = eqN y2 x2"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma lemma_aa [thy_expl]: "eqN x2 x2 = True"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma lemma_ab [thy_expl]: "app x2 NL.Nil = x2"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma lemma_ac [thy_expl]: "app (app x1 y1) z1 = app x1 (app y1 z1)"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma lemma_ad [thy_expl]: "eqN x2 (S x2) = False"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma lemma_ae [thy_expl]: "app (rev x13) (rev y13) = rev (app y13 x13)"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma lemma_af [thy_expl]: "rev (rev x12) = x12"
by (hipster_induct_schemes rev.simps app.simps elem.simps)

lemma unknown [thy_expl]: "elem x (app y z) = elem x (app z y)"
oops

lemma unknown [thy_expl]: "elem x (app y y) = elem x y"
oops

lemma unknown [thy_expl]: "elem x (rev y) = elem x y"
oops

lemma unknown [thy_expl]: "elem (S x) (app y z) = elem (S x) (app z y)"
oops

lemma unknown [thy_expl]: "elem Z (app x y) = elem Z (app y x)"
oops

lemma unknown [thy_expl]: "elem (S x) (app y y) = elem (S x) y"
oops

lemma unknown [thy_expl]: "elem (S x) (rev y) = elem (S x) y"
oops

lemma unknown [thy_expl]: "elem Z (app x x) = elem Z x"
oops

lemma unknown [thy_expl]: "elem Z (rev x) = elem Z x"
oops

lemma unknown [thy_expl]: "elem (S Z) (app x y) = elem (S Z) (app y x)"
oops

lemma unknown [thy_expl]: "elem (S Z) (app x x) = elem (S Z) x"
oops

lemma unknown [thy_expl]: "elem (S Z) (rev x) = elem (S Z) x"
oops

hipster_cond elem app eqN
lemma lemma_ag [thy_expl]: "elem x7 y7 \<Longrightarrow> elem x7 (app y7 z7) = True"
by (hipster_induct_schemes elem.simps app.simps Naturals.eqN.simps)

lemma lemma_ah [thy_expl]: "elem x5 z5 \<Longrightarrow> elem x5 (app y5 z5) = True"
by (hipster_induct_schemes elem.simps app.simps Naturals.eqN.simps)

lemma lemma_ai [thy_expl]: "elem x3 y3 \<Longrightarrow> elem Z (NL.Cons x3 y3) = elem Z y3"
by (hipster_induct_schemes elem.simps app.simps Naturals.eqN.simps)

lemma unknown [thy_expl]: "elem x (app y z) = elem x (app z y)"
oops

lemma unknown [thy_expl]: "elem x (app y y) = elem x y"
oops

lemma unknown [thy_expl]: "elem (S x) (app y z) = elem (S x) (app z y)"
oops

lemma unknown [thy_expl]: "elem Z (app x y) = elem Z (app y x)"
oops

lemma unknown [thy_expl]: "elem (S x) (app y y) = elem (S x) y"
oops

lemma unknown [thy_expl]: "elem Z (app x x) = elem Z x"
oops

lemma unknown [thy_expl]: "elem (S Z) (app x y) = elem (S Z) (app y x)"
oops

lemma unknown [thy_expl]: "elem (S Z) (app x x) = elem (S Z) x"
oops

lemma unknown [thy_expl]: "elem y z \<Longrightarrow> elem x (NL.Cons y z) = elem x z"
oops

lemma unknown [thy_expl]: "elem y z \<Longrightarrow> elem (S x) (NL.Cons y z) = elem (S x) z"
oops

lemma unknown [thy_expl]: "elem x y \<Longrightarrow> elem (S Z) (NL.Cons x y) = elem (S Z) y"
oops

theorem inRev: "elem t ts \<Longrightarrow> elem t (rev ts)"
(*apply(induction ts)  apply(simp_all)  by (metis elem.simps(2) elem02 elem03)*)
(* XXX: for some reason it requires elem.simps(2) to be specified even though elem.simps is
        artificially added within Hipster *)
by (hipster_induct_schemes elem.simps rev.simps)



end



