theory InsertionSort
  imports "$HIPSTER_HOME/IsaHipster"

begin
setup Misc_Data.set_mediumverbose

datatype MyNat = 
  Z
  | Succ "MyNat"

fun leq :: "MyNat => MyNat => bool"
where
  "leq Z w = True"
| "leq q Z = False"
| "leq (Succ q) (Succ w) = leq q w"

hipster leq
lemma lemma_a [thy_expl]: "leq x x"
apply (induct x)
apply simp
apply simp
done

lemma lemma_aa [thy_expl]: "leq x (Succ x)"
apply (induct x)
apply simp
apply simp
done

lemma lemma_ab [thy_expl]: "\<not> leq (Succ x) x"
apply (induct x)
apply simp
apply simp
done

lemma lemma_ac [thy_expl]: "leq y x \<Longrightarrow> \<not> leq (Succ x) y"
apply (induct x arbitrary: y)
apply (metis MyNat.distinct(1) leq.elims(2))
apply (metis MyNat.distinct(1) MyNat.inject leq.elims(1))
done

lemma lemma_ad [thy_expl]: "leq x y \<Longrightarrow> leq x (Succ y)"
apply (induct x arbitrary: y)
apply simp
apply simp
apply (metis MyNat.distinct(1) MyNat.inject leq.elims(2))
  done

fun sorted :: "MyNat list => bool"
where
  "sorted [] = True"
| "sorted [x] = True"
| "sorted (x # y # xs) = ((leq x y) \<and> (sorted (y#xs)))"

fun last :: "'a list \<Rightarrow> 'a" where
  "last ([t]) = t"
| "last (_ # ts) = last ts"

fun ins :: " MyNat => MyNat list => MyNat list"
where
 "ins x [] = [x]"
|"ins x (y#ys) = (if (leq x y) then (x#y#ys) else (y#(ins x ys)))"

hipster sorted ins
lemma lemma_ae [thy_expl]: "ins y [x] = ins x [y]"
  apply (induct x arbitrary: y)
apply simp
using leq.elims(2) apply blast
apply simp
apply (metis MyNat.distinct(1) MyNat.inject leq.elims(1) list.inject)
done

lemma unknown [thy_expl]: "InsertionSort.sorted (ins x y) = InsertionSort.sorted y"
oops

lemma unknown [thy_expl]: "ins y (ins x z) = ins x (ins y z)"
oops

end