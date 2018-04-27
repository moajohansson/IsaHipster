theory Llist_of_tree_of
    imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
codatatype 'a Tree = is_Leaf: Leaf | 
           Node (left: "'a Tree") (val: 'a) (right: "'a Tree")
where
  "left Leaf = Leaf" 
| "right Leaf = Leaf"
  
primcorec chop :: "'a Tree \<Rightarrow> 'a Tree"
where
  "is_Leaf t \<or> is_Leaf (left t) \<and> is_Leaf (right t) \<Longrightarrow> is_Leaf (chop t)"
| "val (chop t) = (if is_Leaf (left t) then val (right t) else val (left t))"
| "left (chop t) = (if is_Leaf (left t) then left (right t) else right t)"
| "right (chop t) = (if is_Leaf (left t) then right (right t) else chop (left t))"

(* Converts Llist to right-leaning tree *)
primcorec tree_of :: "'a Llist \<Rightarrow> 'a Tree"
where
  "lnull xs \<Longrightarrow> is_Leaf (tree_of xs)"
| "left (tree_of xs) = Leaf"
| "val (tree_of xs) = lhd xs"
| "right (tree_of xs) = tree_of (ltl xs)"

primcorec llist_of :: "'a Tree \<Rightarrow> 'a Llist"
where
  "is_Leaf t \<Longrightarrow> lnull (llist_of t)"
| "lhd (llist_of t) = val t"
| "ltl (llist_of t) = llist_of (chop t)"
(*hipster tree_of*)
lemma lemma_a [thy_expl]: "Node Leaf y Leaf = tree_of (LCons y LNil)"
  apply (coinduction  arbitrary: y rule: Llist_of_tree_of.Tree.coinduct_strong)
  by (simp_all add: tree_of.ctr(1))
    
lemma lemma_aa [thy_expl]: "Node Leaf y (tree_of z) = tree_of (LCons y z)"
  apply (coinduction  arbitrary: y z rule: Llist_of_tree_of.Tree.coinduct_strong)
  by simp
(*hipster tree_of llist_of*)
lemma unknown [thy_expl]: "left (left (left y)) = Leaf"
  oops

lemma unknown [thy_expl]: "ltl (ltl (ltl y)) = LNil"
  oops
(*hipster chop*)
lemma unknown [thy_expl]: "left (left (left y)) = Leaf"
  oops
lemma chop_tree_of [simp]: "chop (tree_of xs) = tree_of (ltl xs)"
apply(cases xs)
apply simp_all
done
theorem llist_of_tree_of: "llist_of (tree_of xs) = xs"
  by hipster_coinduct_sledgehammer
apply(coinduction arbitrary: xs)
  by (simp add: chop.code llist_of.code tree_of.ctr(2))
end