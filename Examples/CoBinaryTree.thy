theory CoBinaryTree 
imports "$HIPSTER_HOME/IsaHipster"

begin
setup Misc_Data.set_noisy
setup Tactic_Data.set_sledgehammer_coinduct
(* setup Tactic_Data.set_no_proof *)
setup Misc_Data.set_time (* Print out timing info *)
setup Misc_Data.set_hammer_timeout_medium (* set sledgehammer timeout to 20 s*)

codatatype 'a Tree =  
  Node (left: "'a Tree") (lab: 'a) (right: "'a Tree")

primcorec mirror :: "'a Tree => 'a Tree"
where
  "mirror t = (case t of (Node l x r) \<Rightarrow> Node (mirror r) x (mirror l))"

primcorec tmap :: "('a => 'b) => 'a Tree => 'b Tree"
where
 "tmap f t = (case t of (Node l x r) \<Rightarrow> Node (tmap f l) (f x) (tmap f r))" 
cohipster mirror
lemma lemma_a [thy_expl]: "mirror (mirror y) = y"
  by(coinduction arbitrary: y rule: Tree.coinduct_strong)
    (simp add: Tree.case_eq_if)
    
lemma lemma_aa [thy_expl]: "Node (mirror x2) z (mirror y) = mirror (Node y z x2)"
by (simp add: mirror.code)
  
lemma lemma_ab [thy_expl]: "mirror (Node x2 z (mirror y)) = Node y z (mirror x2)"
  by (metis lemma_a lemma_aa)

lemma lemma_ac [thy_expl]: "mirror (Node (mirror x2) z y) = Node (mirror y) z x2"
  by (metis lemma_a lemma_aa)

cohipster mirror tmap
lemma lemma_ad [thy_expl]: "tmap z (mirror x2) = mirror (tmap z x2)"
by(coinduction arbitrary: x2 z rule: Tree.coinduct_strong)
  (smt Tree.case_eq_if mirror.simps(1) mirror.simps(2) mirror.simps(3) tmap.simps(1) tmap.simps(2) tmap.simps(3))


(*primcorec tsum :: "nat Tree \<Rightarrow> nat Tree \<Rightarrow> nat Tree"
  where "tsum t u = Node (tsum (left t) (left u)) (lab t + lab u) (tsum (right t) (right u))" 
*)
primcorec tsum :: "nat Tree \<Rightarrow> nat Tree \<Rightarrow> nat Tree"
  where  "tsum t u = (case t of (Node tle tx tr) \<Rightarrow> case u of (Node ul ux ur) \<Rightarrow> Node (tsum tle ul) (tx+ux) (tsum tr ur))"

(* Note: for these proofs I needed to increase the timeout in Sledgehammer from 10 to 20 s per proof.
   The default for Sledgehammer when called interactively is 30s. *)
cohipster tsum mirror
lemma lemma_ae [thy_expl]: "tsum y x = tsum x y"
  by(coinduction arbitrary: x y rule: Tree.coinduct_strong)
    (smt Tree.case_eq_if add.commute tsum.simps(1) tsum.simps(2) tsum.simps(3))

lemma lemma_af [thy_expl]: "tsum (tsum x y) z = tsum x (tsum y z)"
  by(coinduction arbitrary: x y z rule: Tree.coinduct_strong)
(smt Tree.case_eq_if ab_semigroup_add_class.add_ac(1) tsum.simps(1) tsum.simps(2) tsum.simps(3))

lemma lemma_ag [thy_expl]: "mirror (tsum y (mirror x)) = tsum x (mirror y)"
by(coinduction arbitrary: x y rule: Tree.coinduct_strong)
  (smt Tree.case_eq_if lemma_ae mirror.simps(1) mirror.simps(2) mirror.simps(3) tsum.simps(1) tsum.simps(2) tsum.simps(3))
  
lemma lemma_ah [thy_expl]: "tsum (mirror x) (mirror y) = mirror (tsum x y)"
  by (metis lemma_a lemma_ae lemma_ag)
    
lemma lemma_ai [thy_expl]: "mirror (tsum x (tsum y (mirror z))) = tsum (mirror (tsum x y)) z"
  by (metis lemma_ae lemma_af lemma_ag)


end