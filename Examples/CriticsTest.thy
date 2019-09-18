theory CriticsTest
imports "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

fun app :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" 
where 
  "app Emp xs = xs"
| "app (Cons x xs) ys = Cons x (app xs ys)"


fun len ::  "'a Lst \<Rightarrow> nat"
where
  "len Emp = 0"
| "len (Cons x xs) = 1 + (len xs)"  
lemma lemma_ab [thy_expl]: "len y + len z = len (app y z)"
apply (induction y)
apply simp
by simp

lemma lemma_ac [thy_expl]: "len (app zz yy) = len (app yy zz)"
apply (induction yy)
apply simp
apply (tactic \<open>Hipster_Explore.explore_goal @{context} ["CriticsTest.app"]\<close>)
(*
apply (metis lemma_a)
apply simp
by (metis SmallListDemo.lemma_ab Suc_eq_plus1_left add.left_commute len.simps(2))
*)
end