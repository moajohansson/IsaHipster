(* From Isabelle exercsises http://isabelle.in.tum.de/exercises/ *)
theory ReplaceRevDel
imports "$HIPSTER_HOME/IsaHipster"

begin

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace x y []     = []"
| "replace x y (z#zs) = (if z=x then y else z)#(replace x y zs)"

  
hipster replace List.append rev
  
primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 x []     = []"
| "del1 x (y#ys) = (if y=x then ys else y # del1 x ys)"

primrec delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "delall x []     = []"
| "delall x (y#ys) = (if y=x then delall x ys else y # delall x ys)"
  
hipster del1 delall
lemma lemma_a [thy_expl]: "delall y (delall y z) = delall y z"
apply (induct z)
by simp_all

lemma lemma_aa [thy_expl]: "delall z (delall y x2) = delall y (delall z x2)"
apply (induct x2)
by simp_all

lemma unknown [thy_expl]: "del1 y (del1 y z) = del1 y z"
oops  
end