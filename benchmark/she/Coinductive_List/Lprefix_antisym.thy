theory Lprefix_antisym
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

coinductive lprefix :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> bool"
where
  LNil_lprefix: "lprefix LNil xs"
| Le_LCons: "lprefix xs ys \<Longrightarrow> lprefix (LCons x xs) (LCons x ys)"

(*hipster lprefix
Fails with 
No code equations for lprefix *)  

theorem lprefix_antisym:  "\<lbrakk> lprefix xs ys; lprefix ys xs \<rbrakk> \<Longrightarrow> xs = ys"
 by hipster_coinduct_sledgehammer

end