theory RoseTree
  imports Main "$HIPSTER_HOME/IsaHipster"
    "~~/src/HOL/Library/BNF_Corec"
begin
(* Set Hipster tactic *)
setup Tactic_Data.set_sledgehammer_coinduct 
setup Misc_Data.set_noisy
setup Misc_Data.set_time
setup Misc_Data.set_hammer_timeout_medium
setup Tactic_Data.set_no_proof
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

(* Finitely branching Rose tree of pot infinite depth from Isabelle tutorial on corecursion. *)
codatatype 'a Tree = 
  Node (lab: 'a) (sub: "'a Tree list")


primcorec tsum :: "nat Tree \<Rightarrow> nat Tree \<Rightarrow> nat Tree"
where "tsum t u = Node (lab t + lab u) (map (\<lambda>(t', u'). tsum t' u') (zip (sub t) (sub u)))" 

primcorec mirror :: "'a Tree \<Rightarrow> 'a Tree"
  where "mirror t = Node (lab t) (rev (sub t))"

primcorec tmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Tree \<Rightarrow> 'b Tree"
  where "tmap f t = Node (f (lab t)) (map (tmap f) (sub t))"

cohipster mirror 
lemma lemma_a [thy_expl]: "mirror (mirror y) = y"
  by (simp add: Tree.expand)

cohipster mirror tsum 
lemma lemma_aa [thy_expl]: "tsum (mirror x) (mirror x) = mirror (tsum x x)"
  by (metis (no_types, lifting) mirror.code mirror.simps(1) mirror.simps(2) rev_map tsum.ctr tsum.simps(1) tsum.simps(2) zip_rev)
    
lemma unknown [thy_expl]: "tsum y x = tsum x y"
  oops
    
lemma unknown [thy_expl]: "tsum (tsum x y) z = tsum x (tsum y z)"
  oops
    
lemma unknown [thy_expl]: "mirror (tsum x (mirror x)) = tsum x (mirror x)"
  oops
    
lemma unknown [thy_expl]: "mirror (tsum x (mirror (tsum x x))) = tsum x (tsum x (mirror x))"
  oops
    
lemma unknown [thy_expl]: "mirror (tsum x (tsum x (mirror x))) = tsum x (mirror (tsum x x))"
  oops
    
lemma unknown [thy_expl]: "tsum (mirror x) (mirror (tsum x x)) = mirror (tsum x (tsum x x))"
  oops

cohipster mirror tmap 
lemma lemma_ab [thy_expl]: "tmap z (mirror x2) = mirror (tmap z x2)"
  by (simp add: mirror.code rev_map tmap.code)

end