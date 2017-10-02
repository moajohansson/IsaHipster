theory Llist_of_tree_of2
    imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
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

primcorec llist_of :: "'a Tree \<Rightarrow> 'a Llist"
where
  "is_Leaf t \<Longrightarrow> lnull (llist_of t)"
| "lhd (llist_of t) = val t"
| "ltl (llist_of t) = llist_of (chop t)"
  
(* Converts Llist to left-leaning tree *)
primcorec tree_of2 :: "'a Llist \<Rightarrow> 'a Tree" where
  "lnull xs \<Longrightarrow> is_Leaf (tree_of2 xs)"
| "val (tree_of2 xs) = lhd xs"
| "left (tree_of2 xs) = tree_of2 (ltl xs)"
| "right (tree_of2 xs) = Leaf"

hipster tree_of2 chop
lemma lemma_a [thy_expl]: "Node Leaf y Leaf = tree_of2 (LCons y LNil)"
  apply (coinduction  arbitrary: y rule: Llist_of_tree_of2.Tree.coinduct_strong)
  by (simp_all add: tree_of2.ctr(1))
    
lemma lemma_aa [thy_expl]: "Node (tree_of2 z) y Leaf = tree_of2 (LCons y z)"
apply (coinduction  arbitrary: y z rule: Llist_of_tree_of2.Tree.coinduct_strong)
  by simp
    
hipster llist_of
lemma unknown [thy_expl]: "left (left y) = Leaf"
  oops

hipster llist_of tree_of2
lemma unknown [thy_expl]: "left (left (left y)) = Leaf"
  oops
     
theorem llist_of_tree_of2 : "llist_of (tree_of2 xs) = xs"
  (*by hipster_coinduct_sledgehammer *)
  apply(coinduction arbitrary: xs rule: Llist.coinduct_strong)
  by (simp add: chop.code llist_of.code tree_of2.simps(4))
end