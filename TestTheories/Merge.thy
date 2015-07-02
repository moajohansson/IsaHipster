theory Merge
imports Main "$HIPSTER_HOME/IsaHipster"
begin

definition leqnat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"leqnat x y = (x \<le> y)"
thm leqnat_def
declare leqnat_def [simp]

(*definition ltnat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"ltnat x y = (x < y)"
*)
primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "le a []     = True"
| "le a (x#xs) = (leqnat a x & le a xs)"

primrec sorted :: "nat list \<Rightarrow> bool" where
  "sorted []     = True"
| "sorted (x#xs) = (le x xs & sorted xs)"

primrec count :: "nat list => nat => nat" where
  "count []     y = 0"
| "count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"

fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
 "merge [] ys = ys" |
 "merge xs [] = xs" |
 "merge (x # xs) (y # ys) = (
   if leqnat x y
     then x # merge xs (y # ys)
     else y # merge (x # xs) ys
 )"

fun msort :: "nat list \<Rightarrow> nat list"
where
 "msort [] = []" |
 "msort [x] = [x]" |
 "msort xs = (
   let half = length xs div 2 in
   merge (msort (take half xs)) (msort (drop half xs))
 )"
ML{* 
@{term "(Orderings.ord_class.less :: nat \<Rightarrow> nat \<Rightarrow> bool) x y"};

@{term "(x<(Groups.zero_class.zero :: nat)) = (False)"}
*}
setup{*Hip_Tac_Ops.toggle_full_types @{context} *}

setup{*Hip_Tac_Ops.set_metis_to @{context} 1000 *}
hipster_cond leqnat le leqnat


(*hipster count merge plus *)


end
