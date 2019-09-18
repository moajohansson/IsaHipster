theory SimpleCake
imports "$HIPSTER_HOME/IsaHipster"
begin

datatype Slice = Cream | Marzipan

datatype Cake = SwedishPiece Slice | BigPiece Slice Cake

fun merge :: "Cake \<Rightarrow> Cake \<Rightarrow> Cake"
where
  "merge (SwedishPiece slice) cake = BigPiece slice cake"
| "merge (BigPiece slice cake1) cake2 = BigPiece slice (merge cake1 cake2)"

hipster merge
lemma lemma_a [thy_expl]: "merge (merge x2 y2) z2 = merge x2 (merge y2 z2)"
by (hipster_induct_simp_metis SimpleCake.merge.simps)

fun like :: "Slice \<Rightarrow> bool"
where 
   "like Cream = False"
  |"like Marzipan = True"

fun dummyAnd :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where 
  "dummyAnd a b = (a \<and> b)"

fun isTasty :: "Cake \<Rightarrow> bool"
where 
  "isTasty (SwedishPiece slice) = like slice"
 |"isTasty (BigPiece slice cake) = (like slice \<and> isTasty cake)"

ML\<open>Syntax.read_prop @{context} "HOL.conj a b = HOL.conj b a"\<close>

hipster merge isTasty HOL.conj
lemma lemma_aa [thy_expl]: "dummyAnd (isTasty x2) (isTasty y2) = isTasty (merge x2 y2)"
by (hipster_induct_simp_metis SimpleCake.dummyAnd.simps SimpleCake.merge.simps SimpleCake.isTasty.simps)

end

