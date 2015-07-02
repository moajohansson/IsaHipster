theory lt
imports Main
        "../data/Natu"
        "$HIPSTER_HOME/IsaHipster"

begin

fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S x2) (S z) = lt x2 z"

hipster lt
lemma lemma_a [thy_expl]: "lt x2 x2 = False"
by (hipster_induct_schemes lt.lt.simps)

lemma lemma_aa [thy_expl]: "lt x2 (S x2) = True"
by (hipster_induct_schemes lt.lt.simps)

lemma lemma_ab [thy_expl]: "lt (S x2) x2 = False"
by (hipster_induct_schemes lt.lt.simps)

hipster_cond lt
lemma lemma_ac [thy_expl]: "lt y2 x2 \<Longrightarrow> lt x2 y2 = False"
by (hipster_induct_schemes lt.lt.simps)

lemma lemma_ad [thy_expl]: "lt y2 x2 \<Longrightarrow> lt Z x2 = True"
by (hipster_induct_schemes lt.lt.simps)

lemma lemma_ae [thy_expl]: "lt x2 y2 \<Longrightarrow> lt x2 (S y2) = True"
by (hipster_induct_schemes lt.lt.simps)

lemma lemma_af [thy_expl]: "lt y2 x2 \<Longrightarrow> lt x2 (S y2) = False"
by (hipster_induct_schemes lt.lt.simps)

lemma lemma_ag [thy_expl]: "lt y1 x1 \<and> lt z1 y1 \<Longrightarrow> lt (S Z) x1 = True"
by (hipster_induct_schemes lt.lt.simps)

lemma unknown [thy_expl]: "lt z x \<and> lt y z \<Longrightarrow> lt x y = False"
oops

lemma unknown [thy_expl]: "lt z y \<and> lt x z \<Longrightarrow> lt x y = True"
oops

lemma unknown [thy_expl]: "lt z x \<and> lt y z \<Longrightarrow> lt x (S y) = False"
oops

lemma unknown [thy_expl]: "lt z y \<and> lt x z \<Longrightarrow> lt x (S y) = True"
oops

lemma unknown [thy_expl]: "lt z x \<and> lt y z \<Longrightarrow> lt (S x) y = False"
oops

lemma unknown [thy_expl]: "lt z y \<and> lt x z \<Longrightarrow> lt (S x) y = True"
oops

lemma unknown [thy_expl]: "lt z x \<and> lt y z \<Longrightarrow> lt (S x) (S y) = False"
oops

lemma unknown [thy_expl]: "lt z y \<and> lt x z \<Longrightarrow> lt (S x) (S y) = True"
oops

end

