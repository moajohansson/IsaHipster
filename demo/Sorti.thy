theory Sorti
imports Main
        "../IsaHipster"

begin

fun sorted2 :: "nat list \<Rightarrow> bool" where
  "sorted2 []                 = True"
| "sorted2 (_ # Nil)          = True"
| "sorted2 (r # (Cons t ts))  = (r \<le> t \<and> sorted2 ( t # ts))"

fun insert :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "insert r []         = Cons r []"
| "insert r (t # ts) = (if r \<le> t then r # (t # ts) else (t # (insert r ts)))"

fun isort2 :: "nat list \<Rightarrow> nat list" where
  "isort2 [] = []"
| "isort2 (t # ts) = insert t (isort2 ts)"


lemma insSortInvar : "sorted2 y \<Longrightarrow> sorted2 (insert x y)"
(*apply(induction y)
apply(simp_all)*)
by hipster_induct_schemes

lemma isortSorts [thy_expl]: "sorted2 (isort2 x)"
(*apply (induction x)
apply simp_all*)
by (hipster_induct_simp_metis insSortInvar)

lemma lemma_ac [thy_expl]: "sorted2 (insert 0 x3) = sorted2 x3"
by (metis insert.simps(1) insert.simps(2) isort2.cases le0 sorted2.elims(3) sorted2.simps(2) sorted2.simps(3))

lemma unknon []: "sorted2 (insert x y) = sorted2 y"
by (hipster_induct_schemes)


lemma unknon' []: "insert 0 (insert x y) = insert x (insert 0 y)"
by (hipster_induct_simp_metis sorted2.simps insert.simps)

lemma unknonb [thy_expl]: "insert x (insert y z) = insert y (insert x z)"
by (hipster_induct_simp_metis sorted2.simps insert.simps)

lemma unknonc [thy_expl]: "insert 0 (isort2 x2) = isort2 (insert 0 x2)"
by (hipster_induct_simp_metis  insert.simps isort2.simps)
(*
lemma unknond [thy_expl]: "sorted2 x3 \<Longrightarrow> isort2 x3 = x3"
by (hipster_induct_schemes sorted2.simps insert.simps isort2.simps)
*)
lemma unknone [thy_expl]: "isort2 (insert x y) = insert x (isort2 y)"
by (hipster_induct_simp_metis sorted2.simps insert.simps isort2.simps)


lemma unknong [thy_expl]: "isort2 (isort2 x) = isort2 x"
by (hipster_induct_simp_metis sorted2.simps insert.simps isort2.simps)

lemma unknoni []: "sorted2 y \<Longrightarrow> sorted2 (insert x y) = True"
by (hipster_induct_schemes sorted2.simps insert.simps isort2.simps)

lemma unknonf [thy_expl]: "sorted2 (isort2 x) = True"
by (hipster_induct_simp_metis unknon sorted2.simps insert.simps isort2.simps)

lemma unknonj [thy_expl]: "sorted2 y \<Longrightarrow> isort2 (insert x y) = insert x y"
by (hipster_induct_schemes sorted2.simps insert.simps isort2.simps)

end
