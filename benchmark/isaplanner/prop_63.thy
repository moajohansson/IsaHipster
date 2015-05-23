theory prop_63
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster lt len last drop *)

(*hipster lt len drop*)
lemma lemma_a [thy_expl]: "lt x2 x2 = False"
by (hipster_induct_schemes lt.simps len.simps)

lemma lemma_aa [thy_expl]: "lt x2 (S x2) = True"
by (hipster_induct_schemes lt.simps len.simps)

lemma lemma_ab [thy_expl]: "lt (S x2) x2 = False"
by (hipster_induct_schemes lt.simps len.simps)

(*hipster_cond lt*)
lemma lemma_ac [thy_expl]: "lt y2 x2 \<Longrightarrow> lt x2 y2 = False"
by (hipster_induct_schemes lt.simps)

lemma lemma_ad [thy_expl]: "lt y2 x2 \<Longrightarrow> lt Z x2 = True"
by (hipster_induct_schemes lt.simps)

lemma lemma_ae [thy_expl]: "lt x2 y2 \<Longrightarrow> lt x2 (S y2) = True"
by (hipster_induct_schemes lt.simps)

lemma lemma_af [thy_expl]: "lt y2 x2 \<Longrightarrow> lt x2 (S y2) = False"
by (hipster_induct_schemes lt.simps)

lemma lemma_ag [thy_expl]: "lt y1 x1 \<and> lt z1 y1 \<Longrightarrow> lt (S Z) x1 = True"
by (hipster_induct_schemes lt.simps)

lemma lemma_ah [thy_expl]: "lt z x \<and> lt y z \<Longrightarrow> lt x y = False"
by (hipster_induct_schemes lt.simps Nat.exhaust)

lemma lemma_ai [thy_expl]: "lt z y \<and> lt x z \<Longrightarrow> lt x y = True"
by (hipster_induct_schemes lt.simps Nat.exhaust)

lemma unknown [thy_expl]: "lt z y \<and> lt x z \<Longrightarrow> lt (S x) y = True"
by (hipster_induct_schemes lt.simps Nat.exhaust)


(*hipster lt len last drop*)
lemma lemma_aj [thy_expl]: "drop x1 Nil2 = Nil2"
by (hipster_induct_schemes lt.simps len.simps last.simps drop.simps)

lemma lemma_ak [thy_expl]: "drop (len x2) x2 = Nil2"
by (hipster_induct_schemes lt.simps len.simps last.simps drop.simps)

lemma lemma_al [thy_expl]: "drop (S Z) (drop x2 y2) = drop (S x2) y2"
by (hipster_induct_schemes lt.simps len.simps last.simps drop.simps)

lemma lemma_am [thy_expl]: "drop (len x4) (drop y4 x4) = Nil2"
by (hipster_induct_schemes lt.simps len.simps last.simps drop.simps)

lemma unknown []: "drop x (drop y z) = drop y (drop x z)"
oops

lemma unknown []: "drop (S x) (drop y z) = drop (S y) (drop x z)"
oops

(*hipster_cond lt len drop*)
lemma lemma_an []: "lt ya2 x2 \<Longrightarrow> drop x2 (Cons2 y2 z2) = drop x2 (Cons2 xa2 z2)"
by (metis lt.simps drop.simps Nat.exhaust)(*
by (hipster_induct_schemes lt.simps len.simps drop.simps)*)

lemma lemma_ao []: "lt z4 x4 \<Longrightarrow> drop x4 (Cons2 y4 Nil2) = Nil2"
by (metis lt.simps drop.simps Nat.exhaust) (*
by (hipster_induct_schemes lt.simps len.simps drop.simps)*)

fun ltlen :: "Nat \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ltlen n x = lt n (len x)"

(*hipster ltlen*)

(*hipster ltlen drop last len*) (*
lemma lemma_anll [thy_expl]: "ltlen Z (drop x2 y2) = ltlen x2 y2"
by (hipster_induct_schemes ltlen.simps drop.simps last.simps len.simps)

lemma lemma_aoll [thy_expl]: "ltlen (S Z) (drop x2 y2) = ltlen (S x2) y2"
by (hipster_induct_schemes ltlen.simps drop.simps last.simps len.simps)

lemma unknown []: "ltlen x (drop y z) = ltlen y (drop x z)"
oops

lemma unknown []: "ltlen (S x) (drop y z) = ltlen (S y) (drop x z)"
oops

*)


  theorem x0 :
    "(lt n (len xs)) ==> ((last (drop n xs)) = (last xs))"
    (*by (hipster_induct_schemes lt.simps len.simps last.simps drop.simps Nat.exhaust)*)
    apply(induction xs arbitrary: n)
    apply(simp_all)
    by (metis len.simps lt.simps last.simps drop.simps Nat.exhaust list.exhaust)

end

