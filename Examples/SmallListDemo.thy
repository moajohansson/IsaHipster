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
apply (induction y)
apply simp
by simp

lemma lemma_aa [thy_expl]: "app (app y z) x2 = app y (app z x2)"
apply (induction y)
apply simp
by simp


fun len ::  "'a Lst \<Rightarrow> nat"
where
  "len Emp = 0"
| "len (Cons x xs) = 1 + (len xs)"  

hipster app len
lemma lemma_ab [thy_expl]: "len y + len z = len (app y z)"
apply (induction y)
apply simp
by simp

lemma lemma_ac [thy_expl]: "len (app z y) = len (app y z)"
apply (induction y)
apply simp
apply (metis lemma_a)
apply simp
by (metis SmallListDemo.lemma_ab Suc_eq_plus1_left add.left_commute len.simps(2))



fun rev :: "'a Lst \<Rightarrow> 'a Lst"
where 
  "rev Emp = Emp"
| "rev (Cons x xs) = app (rev xs) (Cons x Emp)"

hipster rev len
lemma lemma_ad [thy_expl]: "app (SmallListDemo.rev z) (SmallListDemo.rev y) =
SmallListDemo.rev (app y z)"
apply (induction y)
apply simp
apply (metis lemma_a)
apply simp
by (metis lemma_aa)

lemma lemma_ae [thy_expl]: "len (SmallListDemo.rev y) = len y"
apply (induction y)
apply simp
apply simp
by (metis One_nat_def Suc_eq_plus1 Suc_eq_plus1_left lemma_ab len.simps(1) len.simps(2))

lemma lemma_af [thy_expl]: "SmallListDemo.rev (SmallListDemo.rev y) = y"
apply (induction y)
apply simp
apply simp
by (metis Lst.distinct(1) SmallListDemo.rev.simps(1) SmallListDemo.rev.simps(2) app.elims app.simps(2) lemma_a lemma_ad)


fun filt :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" 
where 
  "filt p Emp = Emp"
| "filt p (Cons x xs) = (if (p x) then (Cons x (filt p xs)) else (filt p xs))"

hipster app filt
lemma lemma_ag [thy_expl]: "filt y (filt y z) = filt y z"
apply (induction z)
apply simp
by simp

lemma lemma_ah [thy_expl]: "filt z (filt y x2) = filt y (filt z x2)"
apply (induction x2)
apply simp
by simp

lemma lemma_ai [thy_expl]: "app (filt y z) (filt y x2) = filt y (app z x2)"
apply (induction z)
apply simp
by simp






fun mem :: "'a \<Rightarrow> 'a Lst \<Rightarrow> bool"
where
  "mem x Emp = False"
| "mem x (Cons y ys) = ((x=y) \<or> (mem x ys))"


hipster mem rev
lemma lemma_aj [thy_expl]: "mem y (app x2 (Lst.Cons z x3)) = mem y (Lst.Cons z (app x2 x3))"
apply (induction x2)
apply simp
apply simp
by (metis )

lemma lemma_ak [thy_expl]: "mem y (app z (app z x2)) = mem y (app z x2)"
apply (induction z)
apply simp
apply simp
by (metis SmallListDemo.lemma_aj mem.simps(2))

lemma lemma_al [thy_expl]: "mem y (app z (app x3 x2)) = mem y (app z (app x2 x3))"
apply (induction x2)
apply simp
apply (metis lemma_a)
apply simp
by (metis Lst.distinct(1) Lst.inject SmallListDemo.lemma_aj app.elims lemma_aa mem.simps(2))

lemma lemma_am [thy_expl]: "mem y (SmallListDemo.rev z) = mem y z"
apply (induction z)
apply simp
apply simp
by (metis lemma_a lemma_aj mem.simps(2))

lemma lemma_an [thy_expl]: "mem y (app x2 z) = mem y (app z x2)"
apply (induction x2)
apply simp
apply (metis lemma_a)
apply simp
by (metis SmallListDemo.lemma_aj mem.simps(2))

lemma lemma_ao [thy_expl]: "mem y (app z (SmallListDemo.rev x2)) = mem y (app z x2)"
apply (induction x2)
apply simp
apply simp
by (metis SmallListDemo.rev.simps(1) SmallListDemo.rev.simps(2) lemma_a lemma_aa lemma_ad lemma_af lemma_al)







end
