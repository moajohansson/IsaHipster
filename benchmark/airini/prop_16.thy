theory prop_16
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin

hipster last app rev
lemma lemma_a [thy_expl]: "app x2 NL.Nil = x2"
by (hipster_induct_schemes last.simps app.simps rev.simps)

lemma lemma_aa [thy_expl]: "app (app x1 y1) z1 = app x1 (app y1 z1)"
by (hipster_induct_schemes last.simps app.simps rev.simps)

lemma lemma_ab [thy_expl]: "app (rev x13) (rev y13) = rev (app y13 x13)"
by (hipster_induct_schemes last.simps app.simps rev.simps)

lemma lemma_ac [thy_expl]: "rev (rev x12) = x12"
by (hipster_induct_schemes last.simps app.simps rev.simps)

lemma unknown [thy_expl]: "last (app x x) = last x"
oops

hipster_cond notNil last app rev head
lemma lemma_ad [thy_expl]: "head (app x1 x1) = head x1"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_ae [thy_expl]: "notNil (app x2 x2) = notNil x2"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_af [thy_expl]: "notNil y3 \<Longrightarrow> last (NL.Cons x3 y3) = last y3"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_ag [thy_expl]: "notNil x3 \<Longrightarrow> head (app x3 y3) = head x3"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_ah [thy_expl]: "notNil x3 \<Longrightarrow> notNil (app x3 y3) = True"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_ai [thy_expl]: "notNil y2 \<Longrightarrow> notNil (app x2 y2) = True"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_aj [thy_expl]: "notNil x17 \<Longrightarrow> head (rev x17) = last x17"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_ak [thy_expl]: "notNil x17 \<Longrightarrow> notNil (rev x17) = True"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

lemma lemma_al [thy_expl]: "last (app x17 x17) = last x17"
by (hipster_induct_schemes notNil.simps last.simps app.simps rev.simps head.simps)

theorem firstLast: "ts \<noteq> Nil \<Longrightarrow> head ts = last (rev ts)"
by (hipster_induct_schemes last.simps head.simps rev.simps notNil.simps)

end



