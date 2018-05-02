theory Chop_tmap
    imports Main "~~/src/HOL/Library/BNF_Corec" "$HIPSTER_HOME/IsaHipster"
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

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"
   
primcorec tmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree"
  where "tmap f t = (case t of Leaf \<Rightarrow> Leaf 
         | Node l x r \<Rightarrow> Node (tmap f l) (f x) (tmap f r))" 
hipster chop tmap
lemma unknown [thy_expl]: "left (left (left y)) = Leaf"
  oops
why doesn't this return nicer things?
*)  
    
(*hipster tmap*)
lemma lemma_a [thy_expl]: "tmap y (Node Leaf z Leaf) = Node Leaf (y z) Leaf"
  apply (coinduction  arbitrary: y z rule: Chop_tmap.Tree.coinduct_strong)
by simp
  
lemma lemma_aa [thy_expl]: "Node Leaf (y z) (tmap y x2) = tmap y (Node Leaf z x2)"
apply (coinduction  arbitrary: x2 y z rule: Chop_tmap.Tree.coinduct_strong)
by (simp_all add: tmap.ctr(1))

lemma lemma_ab [thy_expl]: "Node (tmap y z) (y x2) Leaf = tmap y (Node z x2 Leaf)"
apply (coinduction  arbitrary: x2 y z rule: Chop_tmap.Tree.coinduct_strong)
  by (simp_all add: tmap.ctr(1))
    

theorem chop_tmap: "chop (tmap f t) = tmap f (chop t)"
(*by hipster_coinduct_sledgehammer
Failed to apply initial proof method*)
end