theory OBTDemo
imports "$HIPSTER_HOME/IsaHipster"

begin
(*
fun len :: "'a list \<Rightarrow> nat"
where
  "len [] = 0"
| "len (x#xs) = 1 + (len xs)"
hipster len

fun rot :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "rot 0 xs = xs"
| "rot (Suc n) xs = (case xs of [] \<Rightarrow> [] 
                    | (x#xs) \<Rightarrow> rot n (xs @ [x]))"
*)
(* hipster rot  Fucked. Doesn't prove anything despite simple proofs exisitng! Skitprogram.*)


fun rev :: "'a list \<Rightarrow> 'a list"
where
  "rev [] = []"
| "rev (x#xs) = (rev xs) @ [x]"

fun qrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "qrev [] acc = acc"
| "qrev (x#xs) acc = qrev xs (x#acc)"

hipster rev
lemma lemma_a [thy_expl]: "OBTDemo.rev z @ OBTDemo.rev y = OBTDemo.rev (y @ z)"
apply (induction y)
apply simp
by simp

lemma lemma_aa [thy_expl]: "OBTDemo.rev (OBTDemo.rev y) = y"
apply (induction y)
apply simp
apply simp
by (metis List.rev.simps(2) OBTDemo.rev.simps(1) OBTDemo.rev.simps(2) append_Cons append_Nil append_Nil2 lemma_a list.sel(3) rev_is_Nil_conv)

hipster rev qrev
lemma lemma_ab [thy_expl]: "OBTDemo.rev y @ z = qrev y z"
apply (induction y)
apply simp
apply simp
by (metis append_Cons append_Nil append_assoc)

lemma lemma_ac [thy_expl]: "qrev y [] = OBTDemo.rev y"
sledgehammer
apply (induction y)
apply simp
apply simp
by (metis lemma_ab)

end