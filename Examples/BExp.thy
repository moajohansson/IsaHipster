theory BExp
imports Main
        "$HIPSTER_HOME/IsaHipster"
(*uses "../HipSpec.ML"*)

begin


datatype Boolex = 
  Const bool | 
  Var nat | 
  Neg Boolex| 
  And Boolex Boolex

primrec "valbool" :: "Boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" 
  where
  "valbool (Const b) env = b" |
  "valbool (Var x) env = env x" |
  "valbool (Neg b) env = (\<not> valbool b env)" |
  "valbool (And b c) env = (valbool b env \<and> valbool c env)"

datatype Ifex = CIF bool | VIF nat | IF Ifex Ifex Ifex

primrec valif :: "Ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" 
  where
  "valif (CIF b) env = b" |
  "valif (VIF x) env = env x" |
  "valif (IF b t e) env = (if valif b env then valif t env 
                           else valif e env)"

primrec bool2if :: "Boolex \<Rightarrow> Ifex" 
where
  "bool2if (Const b) = CIF b" |
  "bool2if (Var x) = VIF x" |
  "bool2if (Neg b) = IF (bool2if b) (CIF False) (CIF True)" |
  "bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"

hipster valbool valif bool2if
lemma blah: "valbool b env = valif (bool2if b) env" (* It doesn't produce this for some reason..*)
apply (induction b)
apply simp_all

ML \<open>val consts = ["BExp.value", "BExp.valif", "BExp.bool2if" ] ;\<close>

ML \<open>
val lemma_strs = Hipster_Explore.hipspec_explore @{theory} consts;
\<close>
ML\<open>
(* This fails because in Haskell, the constructor IF has been renamed If, so
when conjectures are read back in, it goes wrong, and Isabelle thinks it refers to
an actual if-statement. *)
val [c1,c2,c3,c4,c5,c6,c7] =  (Library.split_lines (Library.trim_line lemma_strs));


(*
val conjs = map (Goal.init o (Thm.cterm_of @{theory}) o (Syntax.read_prop @{context})) conjs1;
*)
\<close>

ML \<open>
map Pretty.writeln (map ((Syntax.pretty_term @{context}) o prop_of) thms);
\<close>

end
