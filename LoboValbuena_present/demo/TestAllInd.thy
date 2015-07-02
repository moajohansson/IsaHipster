theory TestAllInd
imports Main
        "../IsaHipster"

begin

datatype Nat = Z | S Nat

datatype 'a list = Nil2 | Cons2 "'a" "'a list"


fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
| "len (Cons2 y xs) = S (len xs)"

fun drop :: "Nat => 'a list => 'a list" where
"drop (Z) y = y"
| "drop (S z) (Nil2) = Nil2"
| "drop (S z) (Cons2 x2 x3) = drop z x3"

fun head :: "'a list \<Rightarrow> 'a" where
"head (Cons2 x xs) = x"

fun le :: "Nat => Nat => bool" where
  "le Z     y      = True"
| "le y Z      = False"
| "le (S z) (S x2) = le z x2"

fun ix :: "'a list \<Rightarrow> Nat \<Rightarrow> 'a" where
"ix (Cons2 x xs) Z = x"
| "ix (Cons2 x xs) (S y) = ix xs y"

lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)
(*
hipster_cond le ix*)
(*
lemma 1:
  "ALL i. le i (len xs) --> ix xs i = head (drop i xs)"
proof
  fix i
  show "le i (len xs) --> ix xs i = head (drop i xs)"
  proof
    assume "le i (len xs)"
    then show "ix xs i = head (drop i xs)"
      by (induct i arbitrary: xs) (case_tac xs, simp_all)+
  qed
qed
thm 1
thm 1 [rule_format]*)

lemma b2 :
  "!!i. i < length xs ==> xs ! i = hd (List.drop i xs)"
proof -
  fix i
  assume "i < length xs"
  then show "xs ! i = hd (List.drop i xs)"
   apply (induct i arbitrary: xs)
   apply(case_tac xs, simp_all)
   apply(case_tac xs, simp_all)done
qed
thm b2
ML {*
val _ = Isar_Cmd.terminal_proof
val _ = Proof.global_future_terminal_proof
*}
hipster ix
lemma 2:
  "!!i xs. le i (len xs) ==> ix xs i = head (drop i xs)"
proof -
  fix i xs
  assume "le i (len xs)"
  then show "ix xs i = head (drop i xs)"
    apply (induction i xs rule: drop.induct)
    apply(simp_all )
    by (metis ix.elims head.elims ix.simps list.distinct)
qed
thm 2

lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)
lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma aux: "(le z x2 \<and> le za z \<Longrightarrow> le za x2) \<Longrightarrow> le z (S x2) \<and> le (S za) z \<Longrightarrow> le (S za) (S x2)" oops
thm less_induct

lemma tome [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
proof -
  assume "le z y \<and> le x z"
  then show "le x y = True"
    apply(induct x z arbitrary: y rule: le.induct)
    apply(simp_all)
    apply(metis le.simps Nat.exhaust thy_expl)
    apply(case_tac x2)
    apply(simp_all)
    apply(metis le.simps Nat.exhaust thy_expl)
    proof -
      fix za x2
      assume "le z x2 \<and> le za z \<Longrightarrow> le za x2"
      then show "le z (S x2) \<and> le (S za) z \<Longrightarrow> le za x2"
        using assms
        sorry
    qed
qed

lemma 3:
  assumes "i < len xs"
  shows "xs ! i = head (drop i xs)"
  using assms
    by (induct i arbitrary: xs) (case_tac xs, simp_all)+
thm 3

end

