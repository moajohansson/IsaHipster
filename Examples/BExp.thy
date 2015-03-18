theory BExp
imports Main
        "../IsaHipster"
(*uses "../HipSpec.ML"*)

begin
ML_file "../HipsterExplore.ML"

datatype boolex = 
  Const bool | 
  Var nat | 
  Neg boolex| 
  And boolex boolex

primrec "value" :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" 
  where
  "value (Const b) env = b" |
  "value (Var x) env = env x" |
  "value (Neg b) env = (\<not> value b env)" |
  "value (And b c) env = (value b env \<and> value c env)"

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex

primrec valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" 
  where
  "valif (CIF b) env = b" |
  "valif (VIF x) env = env x" |
  "valif (IF b t e) env = (if valif b env then valif t env 
                           else valif e env)"

primrec bool2if :: "boolex \<Rightarrow> ifex" 
where
  "bool2if (Const b) = CIF b" |
  "bool2if (Var x) = VIF x" |
  "bool2if (Neg b) = IF (bool2if b) (CIF False) (CIF True)" |
  "bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"




ML {* val consts = ["BExp.value", "BExp.valif", "BExp.bool2if" ] ; *}

ML {* 
val lemma_strs = Hipster_Explore.hipspec_explore @{theory} consts;
*}
ML{*
(* This fails because in Haskell, the constructor IF has been renamed If, so
when conjectures are read back in, it goes wrong, and Isabelle thinks it refers to
an actual if-statement. *)
val [c1,c2,c3,c4,c5,c6,c7] =  (Library.split_lines (Library.trim_line lemma_strs));


(*
val conjs = map (Goal.init o (Thm.cterm_of @{theory}) o (Syntax.read_prop @{context})) conjs1;
*)
*}

ML {*
map Pretty.writeln (map ((Syntax.pretty_term @{context}) o prop_of) thms);
*}

end