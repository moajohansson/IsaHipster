theory Lzip_ltakeWhile_fst
  imports Main "$HIPSTER_HOME/IsaHipster"
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

  
fun fst2 :: "('a,'b) Pair2 \<Rightarrow> 'a" where
"fst2 (Pair2 a b) = a"
(*hipster lzip ltakeWhile fst2
Proving: fst2 (Pair22 x2 z) = x2 
Undefined fact: "Lzip_ltakeWhile_fst.Pair2.coinduct_strong" *)
theorem lzip_ltakeWhile_fst: "lzip (ltakeWhile P xs) ys = ltakeWhile (P \<circ> fst2) (lzip xs ys)"
by hipster_coinduct_sledgehammer
end