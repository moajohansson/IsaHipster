theory TestThingolSorted
  imports "$HIPSTER_HOME/IsaHipster"
begin    
setup Misc_Data.set_noisy
setup Tactic_Data.set_recinduct_sledgehammer
setup Misc_Data.set_bool_eq_split

fun sorted :: "nat list \<Rightarrow> bool"
  where "sorted [] = True"
  | "sorted [x] = True"
  | "sorted (x1#x2#xs) = ((x1 \<le> x2) \<and> sorted (x2#xs))"

fun ins :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where "ins x [] = [x]"
  | "ins x (y#ys) = (if (x \<le> y) then (x#y#ys) else y#(ins x ys))"

fun isort ::  "nat list \<Rightarrow> nat list"
  where "isort [] = []"
  | "isort (x#xs) = ins x (isort xs)"

(* hipster sorted isort ins *)
ML\<open>
Code_Thingol.consts_program @{context} ["TestThingolSorted.sorted"]
\<close>
export_code sorted isort ins in Thingol

















end