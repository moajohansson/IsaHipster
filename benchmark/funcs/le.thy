theory le
imports Main
        "../data/Natu"
        "../../IsaHipster"

begin

fun le :: "Nat => Nat => bool" where
  "le Z     y      = True"
| "le y Z      = False"
| "le (S z) (S x2) = le z x2"

(*hipster le*)

lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.le.simps)

(*hipster_cond le*)
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.le.simps)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.le.simps)

(* false
lemma unknown [thy_expl]: "le y y \<and> le x z \<Longrightarrow> le x (S Z) = le x (S y)"
oops *)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

ML {*
fun rprems_tac ctxt = Goal.norm_hhf_tac ctxt THEN' CSUBGOAL (fn (goal, i) =>
      let
        fun non_atomic (Const ("==>", _) $ _ $ _) = true
          | non_atomic (Const ("all", _) $ _) = true
          | non_atomic _ = false;

        val ((_, goal'), ctxt') = Variable.focus_cterm goal ctxt;
        val goal'' = Drule.cterm_rule 
          (singleton (Variable.export ctxt' ctxt)) goal';
        val Rs = filter (non_atomic o Thm.term_of) 
          (Drule.strip_imp_prems goal'');
        val _ = @{print} Rs
        val _ = @{print} goal''

        val ethms = Rs |> map (fn R =>
          (Raw_Simplifier.norm_hhf ctxt' (Thm.trivial R)));
      in eresolve_tac ethms i end
  ); *}

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x (S y) = True"
oops

lemma unknown [thy_expl]: "le z x \<and> le y z \<Longrightarrow> le (S x) y = False"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le (S x) (S y) = True"
oops

(* false
lemma unknown [thy_expl]: "le x z \<and> le z z \<Longrightarrow> le x (S y) = True"
oops *)

end

