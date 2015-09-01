theory Sor
imports Main
        "$HIPSTER_HOME/IsaHipster"

begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
  | "sorted (Cons2 y (Nil2)) = True"
  | "sorted (Cons2 y (Cons2 y2 ys)) =
       (if le y y2 then sorted (Cons2 y2 ys) else False)"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  (*hipster le sorted insort sort *)
(*hipster le*)
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

lemma unknown [thy_expl]: "insort x (insort y z) = insort y (insort x z)"
oops

lemma unknown [thy_expl]: "insort Z (insort x y) = insort x (insort Z y)"
oops

(*hipster_cond le*)
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_af [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

(*fun nole:: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "nole x y = (\<not> le x y)"

hipster_cond nole
lemma lemma_ag [thy_expl]: "nole (S x2) y2 = le y2 x2"
by (hipster_induct_schemes Sor.nole.simps Sor.Nat.exhaust)

lemma lemma_ah [thy_expl]: "nole x2 y2 \<Longrightarrow> nole x2 Z = True"
by (hipster_induct_schemes Sor.nole.simps Sor.Nat.exhaust)*)

hipster sorted insort le
lemma lemma_ag [thy_expl]: "insort Z (insort x19 y19) = insort x19 (insort Z y19)"
by (hipster_induct_schemes sorted.simps insort.simps le.simps list.exhaust Nat.exhaust)

lemma lemma_ah [thy_expl]: "sorted (insort Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps insort.simps le.simps list.exhaust Nat.exhaust)

lemma unknown [thy_expl]: "insort x (insort y z) = insort y (insort x z)"
oops

lemma unknown [thy_expl]: "sorted (insort x y) = sorted y"
oops
(*lemma lemma_ag [thy_expl]: "insort Z (insort x2 y2) = insort x2 (insort Z y2)"
by (hipster_induct_schemes insort.simps le.simps)

(*hipster_cond sorted insort*)
lemma lemma_ah [thy_expl]: "sorted (insort Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps insort.simps)*)

hipster_cond sorted insort
lemma unknown [thy_expl]: "Sor.insort x (Sor.insort y z) = Sor.insort y (Sor.insort x z)"
oops

lemma unknown [thy_expl]: "Sor.sorted (Sor.insort x y) = Sor.sorted y"
oops

lemma unknown [thy_expl]: "Sor.sorted y \<Longrightarrow> Sor.sorted (Sor.insort x y) = True"
oops


fun nole:: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "nole x y = (\<not> le x y)"

(*hipster_cond nole*)
(*hipster nole le*)
lemma lemma_ai [thy_expl]: "le (S x2) y2 = nole y2 x2"
by (hipster_induct_schemes nole.simps)

lemma lemma_aj [thy_expl]: "nole x2 y2 \<Longrightarrow> le x2 Z = False"
by (hipster_induct_schemes le.simps nole.simps)

ML{*
  val _ = Local_Defs.unfold_tac
  val _ = Raw_Simplifier.rewrite_goals_rule
  val simple_prover = SINGLE o (fn ctxt => ALLGOALS (resolve_tac (Raw_Simplifier.prems_of ctxt)));
  val _ =   Conv.fconv_rule (Conv.prems_conv ~1 (Raw_Simplifier.rewrite_cterm (true, true, true) simple_prover
    (empty_simpset @{context} addsimps @{thms nole.simps})))
  val _ = Pattern.rewrite_term
*}

setup{* Hip_Tac_Ops.toggle_full_types @{context} ;*}
setup{* Hip_Tac_Ops.set_metis_to @{context} 1000;*}

lemma lemma_ak [thy_expl]: "sorted y \<Longrightarrow> sorted (insort x y) = True"
by (hipster_induct_schemes sorted.simps nole.simps insort.simps le.simps)
(*
apply(induction y arbitrary: x rule: sorted.induct)
apply(simp_all)
apply(metis nole.simps thy_expl)
by(metis (full_types) thy_expl sorted.simps insort.simps nole.simps)*)

  theorem x0 :
    "sorted (sort xs)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
