theory Lappend_inf
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
  
primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"
  
inductive lfinite :: "'a Llist \<Rightarrow> bool" 
where
  lfinite_LNil:  "lfinite LNil"
| lfinite_LConsI: "lfinite xs \<Longrightarrow> lfinite (LCons x xs)"

(* hipster lappend lfinite
Fails because: No code equations for lfinite
*)
theorem  "\<not> lfinite xs \<Longrightarrow> lappend xs ys = xs"
  by hipster_coinduct_sledgehammer
end
  