theory Sunfold
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
primcorec sunfold :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "sunfold g f a = SCons (g a) (sunfold g f (f a))"

(*cohipster sunfold shd stl Fun.id*)
(* ca 30 sec *)
lemma lemma_a [thy_expl]: "sunfold id y (y z) = sunfold y y z"
 by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto

lemma lemma_aa [thy_expl]: "sunfold id id (y z) = sunfold y id z"
 by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto

lemma lemma_ab [thy_expl]: "SCons z (sunfold y y z) = sunfold id y z"
 by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_a)

lemma lemma_ac [thy_expl]: "SCons (y z) (sunfold y id z) = sunfold y id z"
 by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    simp
(*cohipster sunfold Fun.comp*)
(* ca 25 sec *)
(* Special case of fusion law *)
lemma lemma_ad [thy_expl]: "sunfold (z \<circ> x2) x2 x3 = sunfold z x2 (x2 x3)"
 by (coinduction arbitrary: x2 x3 z rule: Stream.Stream.coinduct_strong)
    auto
end