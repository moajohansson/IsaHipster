theory SmallListDemo
imports "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

fun app :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" 
where 
  "app Emp xs = xs"
| "app (Cons x xs) ys = Cons x (app xs ys)"

hipster app
lemma lemma_a [thy_expl]: "app y Emp = y"
  apply (induct y)
  by simp_all
    
lemma lemma_aa [thy_expl]: "app (app y z) x2 = app y (app z x2)"
  apply (induct y arbitrary: x2 z)
  by simp_all

fun len ::  "'a Lst \<Rightarrow> nat"
where
  "len Emp = 0"
| "len (Cons x xs) = 1 + (len xs)"  

(* hipster app len *)
lemma lemma_ab [thy_expl]: "len y + len z = len (app y z)"
  apply (induct y arbitrary: z)
  by simp_all

fun rev :: "'a Lst \<Rightarrow> 'a Lst"
where 
  "rev Emp = Emp"
| "rev (Cons x xs) = app (rev xs) (Cons x Emp)"

(*hipster rev len *)
lemma lemma_ac [thy_expl]: "app (SmallListDemo.rev z) (SmallListDemo.rev y) =
SmallListDemo.rev (app y z)"
  apply hipster_induct
  apply (induct y arbitrary: z)
  apply (simp_all add: lemma_a)
  by (metis lemma_aa)
    
lemma lemma_ad [thy_expl]: "len (SmallListDemo.rev y) = len y"
  apply (induct y)
  apply simp_all
  by (metis One_nat_def Suc_eq_plus1 Suc_eq_plus1_left lemma_ab len.simps(1) len.simps(2))
    
lemma lemma_ae [thy_expl]: "SmallListDemo.rev (SmallListDemo.rev y) = y"
  apply (induct y)
  apply simp_all
  by (metis Lst.distinct(1) SmallListDemo.rev.simps(1) SmallListDemo.rev.simps(2) app.elims app.simps(2) lemma_ac)


fun filt :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" 
where 
  "filt p Emp = Emp"
| "filt p (Cons x xs) = (if (p x) then (Cons x (filt p xs)) else (filt p xs))"

hipster app filt
lemma lemma_af [thy_expl]: "filt y (filt y z) = filt y z"
  apply (induct z)
  by simp_all
    
lemma lemma_ag [thy_expl]: "filt z (filt y x2) = filt y (filt z x2)"
  apply (induct x2)
  by simp_all
    
lemma lemma_ah [thy_expl]: "app (filt y z) (filt y x2) = filt y (app z x2)"
  apply (induct z arbitrary: x2)
  by simp_all



fun mem :: "'a \<Rightarrow> 'a Lst \<Rightarrow> bool"
where
  "mem x Emp = False"
| "mem x (Cons y ys) = ((x=y) \<or> (mem x ys))"


hipster mem rev
lemma lemma_ai [thy_expl]: "mem y (app x2 (Lst.Cons z x3)) = mem y (Lst.Cons z (app x2 x3))"
  apply (induct x2 arbitrary: x3)
  apply simp_all
  by auto
    
lemma lemma_aj [thy_expl]: "mem y (app z (app z x2)) = mem y (app z x2)"
  apply (induct z arbitrary: x2)
  by (simp_all add: lemma_ai)
    
lemma lemma_ak [thy_expl]: "mem y (app z (app x3 x2)) = mem y (app z (app x2 x3))"
  apply (induct x2 arbitrary: x3 z)
  apply (simp_all add: lemma_a)
  by (metis lemma_aa lemma_ai mem.simps(2))
    
lemma lemma_al [thy_expl]: "mem y (SmallListDemo.rev z) = mem y z"
  apply (induct z)
  by (simp_all add: lemma_a lemma_ai)
    
lemma lemma_am [thy_expl]: "mem y (app z (SmallListDemo.rev x2)) = mem y (app z x2)"
  apply (induct x2 arbitrary: z)
  apply simp_all
  by (smt SmallListDemo.rev.simps(2) app.simps(2) lemma_ac lemma_ae lemma_ai lemma_al mem.simps(2))





end
