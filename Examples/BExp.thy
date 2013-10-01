theory BExp
imports Main
uses "HipSpec.ML"

begin

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



ML{*
val filepath = "~/TheoremProvers/IsaHip/";
val hipspecifyer_cmd = filepath^"HipSpecifyer";
val modulenm = "BExp";
val consts = map (fn x => modulenm^"."^x) ["value", "valif", "bool2if"];

HipSpec.hipspec @{theory} hipspecifyer_cmd filepath modulenm consts;

*}

end