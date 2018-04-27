theory Lappend_literates
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
 primcorec literates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literates f x = LCons x (literates f (f x))"

primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"

(* Need obs to explore with literates *)
 datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
lemma "\<exists>(n::integer). n < 0"  
  using neg_less_0_iff_less zero_less_one by blast
lemma integerz [simp]: "(\<forall>(n::integer). \<not> n \<le> 0) \<Longrightarrow> False"
  by blast
fun obsLList :: "int \<Rightarrow> 'a Llist \<Rightarrow> 'a Lst" where
"obsLList n s = (if (n \<le> 0) then Emp else Cons (lhd s) (obsLList (n - 1) (ltl s)))"

(*hipster_obs Llist Lst obsLList literates lappend*)
lemma lemma_a [thy_expl]: "lappend (literates z x2) y = literates z x2"
  apply (coinduction  arbitrary: x2 y z rule: Lappend_literates.Llist.coinduct_strong)
  apply simp
  by auto
  
lemma lemma_aa [thy_expl]: "lappend (LCons z (literates x2 x3)) y = LCons z (literates x2 x3)"
  apply (coinduction  arbitrary: x2 x3 y z rule: Lappend_literates.Llist.coinduct_strong)
  by (simp_all add: lemma_a)
 
theorem lappend_literates: "lappend (literates f x) xs = literates f x"
(*by hipster_coinduct_sledgehammer works from the start *)
by (simp add: lemma_a)
end