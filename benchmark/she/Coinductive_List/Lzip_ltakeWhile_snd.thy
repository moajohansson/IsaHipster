theory Lzip_ltakeWhile_snd
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
primcorec ltakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "lnull xs \<or> \<not> P (lhd xs) \<Longrightarrow> lnull (ltakeWhile P xs)"
| "lhd (ltakeWhile P xs) = lhd xs"
| "ltl (ltakeWhile P xs) = ltakeWhile P (ltl xs)"
datatype ('a, 'b) Pair2 = Pair2 'a 'b 

primcorec lzip :: "'a Llist \<Rightarrow> 'b Llist \<Rightarrow> (('a, 'b) Pair2) Llist"
where
  "lnull xs \<or> lnull ys \<Longrightarrow> lnull (lzip xs ys)"
| "lhd (lzip xs ys) = (Pair2 (lhd xs) (lhd ys))"
| "ltl (lzip xs ys) = lzip (ltl xs) (ltl ys)"  

fun snd2 :: "('a,'b) Pair2 \<Rightarrow> 'b" where
"snd2 (Pair2 a b) = b"

theorem lzip_ltakeWhile_snd: "lzip xs (ltakeWhile P ys) = ltakeWhile (P \<circ> snd2) (lzip xs ys)"
by hipster_coinduct_sledgehammer
end