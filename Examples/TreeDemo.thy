theory TreeDemo
imports "../IsaHipster"

begin

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree""'a Tree"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

fun tmap :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "tmap f (Leaf x) = Leaf (f x)"
| "tmap f (Node l r) = Node (tmap f l) (tmap f r)" 

(* First call to Hipster: Explore tmap and mirror *)
ML{* Hipster_Explore.explore  @{context} ["TreeDemo.tmap", "TreeDemo.mirror"]; *}



fun flat_tree :: "'a Tree => 'a list"
where
  "flat_tree (Leaf x) = [x]"
| "flat_tree (Node l r) = (flat_tree l) @ (flat_tree r)"

(* Second call to Hipster: Explore relation to lists *)
ML{*Hipster_Explore.explore  @{context} ["TreeDemo.flat_tree", "TreeDemo.mirror", "TreeDemo.tmap", 
                                         "List.rev", "List.map"]; *}


fun rigthmost :: "'a Tree \<Rightarrow> 'a"
where 
  "rigthmost (Leaf x) = x"
|  "rigthmost (Node l r) = rigthmost r"

fun leftmost :: "'a Tree \<Rightarrow> 'a"
where 
  "leftmost (Leaf x) = x"
|  "leftmost (Node l r) = leftmost l"

(* Third call to Hipster: Rightmost and Leftmost element of a tree. *)
ML{* Hipster_Explore.explore  @{context} ["List.hd", "List.rev","TreeDemo.mirror","TreeDemo.flat_tree", 
                                          "TreeDemo.rigthmost", "TreeDemo.leftmost"]; *}


ML{* Hipster_Explore.explore  @{context} ["List.last", "List.rev","TreeDemo.mirror","TreeDemo.flat_tree", 
                                          "TreeDemo.rigthmost", "TreeDemo.leftmost"]; *}

end
