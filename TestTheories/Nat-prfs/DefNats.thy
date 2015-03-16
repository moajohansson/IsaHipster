theory DefNats
imports "../Naturals"

begin

(* less or equal to Z *)
definition leZ :: "Nat => bool" where
  "leZ x = (x = Z)"

(* greater or equal to Z *)
definition geZ :: "Nat => bool" where
  "geZ _ = True"

definition less :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "less a b = (leq a b \<and> \<not> leq b a)"

definition greater :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "greater a b = (geq a b \<and> (\<not> geq b a))"

definition leZZ :: "Nat \<Rightarrow> bool" where
  "leZZ x = eqN x Z"


(* TEST: hipster leq leZZ *)
lemma unknown2 [thy_expl]: "leZZ (S x) = False"
by(simp add: leZZ_def)

(* hipster_cond leZ add mul leq *)

(* hipster_cond leZ add leq
hipster_cond (leq x) leq leZ *)

(* for some reason, Naturals.leZ.simps appears BUT it should be Naturals.leZ_def since it is a definition...
    is it because we ourselves add it artificially to the simpset somewhere? or what is behind the appearance
    of leZ as a function with an associated simplification rule? *)
(* Uncomment: hipster_cond leZ leq *)
lemma unknown [thy_expl]: "leq x Z = leZ x" oops (*apply(induction x) apply(simp_all add: leZ_def)*)
lemma unknown [thy_expl]: "leZ Z = True" oops (* by (metis leZ_def) *)
lemma unknown [thy_expl]: "leZ (S x) = False" oops (* by (simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ (S Z) = False" oops (* by (simp add: leZ_def) BUT: is actually simpler than prior cases *)
lemma unknown [thy_expl]: "leq (S x) (S Z) = leZ x" oops (* redundant *)
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> Z = x" oops (* again ... apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> leq x y = True" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> leq x (S y) = True" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<Longrightarrow> leq (S x) y = False" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> leq (S x) (S y) = True" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<and> leZ x \<Longrightarrow> x = y"  oops (* apply(simp add: leZ_def) *)

(*
(* cannot use \<Longleftrightarrow> ... is it because of the definitional nature of lt lifting it into meta-equality? *) 
lemma lesslt : "less m n = lt m n"
apply(auto)
apply(induction m)
*)

end
