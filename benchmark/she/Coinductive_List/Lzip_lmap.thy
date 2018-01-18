theory Lzip_lmap
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_induct_and_coinduct_sledgehammer  

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

fun map_prod2 :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a,'b) Pair2 \<Rightarrow> ('c,'d) Pair2" where
"map_prod2 f g (Pair2 a b) = Pair2 (f a) (g b)"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  
hipster map_prod2 lzip lmap
lemma lemma_a [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
  apply (coinduction  arbitrary: y z rule: Lzip_lmap.Llist.coinduct_strong)
  by simp

lemma lemma_aa [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
  apply (coinduction  arbitrary: x2 y z rule: Lzip_lmap.Llist.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "ltl (lmap y z) = lmap y (ltl z)"
apply (coinduction  arbitrary: y z rule: Lzip_lmap.Llist.coinduct_strong)
apply simp
by (smt Llist.case_eq_if Llist.disc(1) Llist.disc_eq_case(1) Llist.sel(1) Llist.simps(5) lmap.code ltl_def)

lemma unknown [thy_expl]: "ltl (ltl z) = LNil"
oops

lemma unknown [thy_expl]: "ltl (ltl (ltl y)) = LNil"
  oops 

theorem lzip_lmap:
  "lzip (lmap f xs) (lmap g ys) = lmap (map_prod2 f g) (lzip xs ys)"
  apply(coinduction arbitrary: f g xs ys rule: Llist.coinduct_strong)
  by (smt Llist.case_eq_if Llist.sel(1) lemma_ab lmap.disc_iff(2) lmap.sel(1) lzip.ctr(2) lzip.disc(1) lzip.disc(2) lzip.simps(4) map_prod2.simps)
(*by hipster_coinduct_sledgehammer
  Failed to apply initial proof method *)  
    (* sledgehammer timed out before exploration*)
end