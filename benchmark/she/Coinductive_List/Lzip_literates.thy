theory Lzip_literates
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
datatype ('a, 'b) Pair2 = Pair2 'a 'b 

primcorec lzip :: "'a Llist \<Rightarrow> 'b Llist \<Rightarrow> (('a, 'b) Pair2) Llist"
where
  "lnull xs \<or> lnull ys \<Longrightarrow> lnull (lzip xs ys)"
| "lhd (lzip xs ys) = (Pair2 (lhd xs) (lhd ys))"
| "ltl (lzip xs ys) = lzip (ltl xs) (ltl ys)"
  
primcorec literates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
  where "literates f x = LCons x (literates f (f x))"
    
fun map_prod2 :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a,'b) Pair2 \<Rightarrow> ('c,'d) Pair2" where
"map_prod2 f g (Pair2 a b) = Pair2 (f a) (g b)"

theorem lzip_literates:
  "lzip (literates f x) (literates g y) = literates (map_prod2 f g) (Pair2 x y)"
by hipster_coinduct_sledgehammer
end