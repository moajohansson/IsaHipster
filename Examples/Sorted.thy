theory Sorted
imports "../IsaHipster"

begin
datatype Nat = 
  Z
  | Succ "Nat"

fun leq :: "Nat => Nat => bool"
where
  "leq Z y = True"
| "leq x Z = False"
| "leq (Succ x) (Succ y) = leq x y"

hipster leq
lemma lemma_a [thy_expl]: "leq (Succ x2) (Succ x2) = True"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Sorted.leq.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "leq (Succ x2) x2 = False"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Sorted.leq.simps thy_expl} *})

lemma lemma_ab [thy_expl]: "leq x2 (Succ x2) = True"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Sorted.leq.simps thy_expl} *})

fun sorted :: "Nat list => bool"
where
  "sorted [] = True"
| "sorted [x] = True"
| "sorted (x # y # xs) = ((leq x y) \<and> (sorted (y#xs)))"
thm sorted.induct

fun last :: "'a list \<Rightarrow> 'a" where
  "last ([t]) = t"
| "last (_ # ts) = last ts"
thm last.induct

fun ins :: " Nat => Nat list => Nat list"
where
 "ins x [] = [x]"
|"ins x (y#ys) = (if (leq x y) then (x#y#ys) else (y#(ins x ys)))"
thm ins.induct

hipster sorted ins
lemma lemma_ac [thy_expl]: "leq x2 x2 = True"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Sorted.sorted.simps Sorted.ins.simps thy_expl} *})

lemma lemma_ad [thy_expl]: "Sorted.sorted (ins Z x2) = Sorted.sorted x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Sorted.sorted.simps Sorted.ins.simps thy_expl} *})

lemma unknown [thy_expl]: "ins Z (ins x y) = ins x (ins Z y)"
oops

lemma unknown [thy_expl]: "ins x (ins y z) = ins y (ins x z)"
oops

lemma unknown [thy_expl]: "Sorted.sorted (ins x y) = Sorted.sorted y"
oops

fun isort :: "Nat list => Nat list"
where
  "isort [] = []"
| "isort (x#xs) = ins x (isort xs)"

hipster_cond sorted isort leq sorted ins
lemma lemma_ae [thy_expl]: "ins Z (isort x2) = isort (ins Z x2)"
by (hipster_induct_simp_metis Sorted.sorted.simps Sorted.isort.simps Sorted.leq.simps Sorted.sorted.simps Sorted.ins.simps)

lemma unknown [thy_expl]: "ins x (ins y z) = ins y (ins x z)"
oops

lemma unknown [thy_expl]: "Sorted.sorted (ins x y) = Sorted.sorted y"
oops

lemma unknown [thy_expl]: "isort (ins x y) = ins x (isort y)"
oops

lemma unknown [thy_expl]: "Sorted.sorted (isort x) = True"
oops

lemma unknown [thy_expl]: "isort (isort x) = isort x"
oops

lemma unknown [thy_expl]: "ins Z (ins x y) = ins x (ins Z y)"
oops

lemma unknown [thy_expl]: "Sorted.sorted x \<Longrightarrow> isort x = x"
oops

lemma unknown [thy_expl]: "Sorted.sorted y \<Longrightarrow> Sorted.sorted (ins x y) = True"
oops

lemma unknown [thy_expl]: "Sorted.sorted y \<Longrightarrow> isort (ins x y) = ins x y"
oops

lemma unknown [thy_expl]: "Sorted.sorted x \<Longrightarrow> isort (ins Z x) = ins Z x"
oops

end
