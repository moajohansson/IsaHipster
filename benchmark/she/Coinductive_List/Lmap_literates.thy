theory Lmap_literates
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
primcorec literates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literates f x = LCons x (literates f (f x))"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

(* Need obs to explore with literates *)
codatatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

fun obsLList :: "int \<Rightarrow> 'a Llist \<Rightarrow> 'a Lst" where
"obsLList n s = (if (n \<le> 0) then Emp else Cons (lhd s) (obsLList (n - 1) (ltl s)))"
lemma stuff: "lhd (lmap z (literates y x2)) = z x2"
    by (simp add: Llist.case_eq_if)
(*hipster_obs Llist Lst obsLList literates lmap*)
lemma lemma_a [thy_expl]: "lmap y (literates y z) = literates y (y z)"
apply (coinduction  arbitrary: y z rule: Lmap_literates.Llist.coinduct_strong)
  apply simp
  by (metis (no_types, lifting) Llist.case_eq_if literates.disc_iff literates.simps(2) literates.simps(3))

lemma lemma_aa [thy_expl]: "lmap z (LCons y (literates z x2)) = LCons (z y) (literates z (z x2))"
apply (coinduction  arbitrary: x2 y z rule: Lmap_literates.Llist.coinduct_strong)
  by (simp_all add: lemma_a)
(* Why isn't obs function in background? Bug somewhere! *)    
lemma lemma_ab [thy_expl]: "obsLList 1 (lmap z (literates y x2)) = Lst.Cons (z x2) Emp"
apply (coinduction  arbitrary: x2 y z rule: Lmap_literates.Lst.coinduct_strong)
  by (simp_all add: Llist.case_eq_if)
    
lemma lemma_ac [thy_expl]: "ltl (lmap y (literates z x2)) = lmap y (literates z (z x2))"
apply (coinduction  arbitrary: x2 y z rule: Lmap_literates.Llist.coinduct_strong)
by (simp_all add: Llist.case_eq_if)
(*Proving: lhd (lmap z (literates y x2)) = z x2 
No matching coinduction rule found*)  
theorem lmap_literates: "lmap f (literates f x) = literates f (f x)"
  by(simp add: lemma_a)
  (*by hipster_coinduct_sledgehammer
Metis: Failed to replay Metis proof
resynchronize: Out of sync 
Failed to apply initial proof method *)
  apply(coinduction arbitrary: x rule: Llist.coinduct_strong)
  by (smt Llist.case_eq_if literates.disc_iff literates.simps(2) literates.simps(3) lmap.disc_iff(2) lmap.sel(1) lmap.sel(2))
(*by hipster_coinduct_sledgehammer
fails *)
end