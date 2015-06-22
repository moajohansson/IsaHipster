theory BinTree
imports Main
        "../IsaHipster"

begin

datatype 'a binTree = Leaf 'a | Node 'a "('a binTree)" "('a binTree)"

fun is_leaf :: "'a binTree \<Rightarrow> bool" where
  "is_leaf (Leaf _)     = True"
| "is_leaf (Node _ _ _) = False"

fun mirror :: "'a binTree \<Rightarrow> 'a binTree" where
  "mirror (Leaf b)     = Leaf b"
| "mirror (Node b l r) = Node b (mirror r) (mirror l)"

fun tree_size :: "'a binTree \<Rightarrow> nat" where
  "tree_size (Leaf b)     = 1"
| "tree_size (Node _ l r) = 1 + tree_size l + tree_size r"

fun tree_height :: "'a binTree \<Rightarrow> nat" where
  "tree_height (Leaf _)     = 1"
| "tree_height (Node _ l r) = 1 + max (tree_height l) (tree_height r)"

fun flat_tree :: "'a binTree \<Rightarrow> 'a list" where
  "flat_tree (Leaf b)     = [b]"
| "flat_tree (Node b l r) = (flat_tree l) @  (b # (flat_tree r))"

(* http://www.labri.fr/perso/casteran/FM/Logique/C4.pdf *)
lemma tree_decompose : "tree_size t \<noteq> 1 \<Longrightarrow> \<exists> n l r . t = Node n l r"
by (metis tree_size.elims)  (* reminder: should fiddle with our metis wrapper/routine tacs *)
(* by hipster_induct_simp_metis *)

lemma le_height_size : "tree_height t \<le> tree_size t"
by hipster_induct_simp_metis
(* ----- *)

lemma lemma_a [thy_expl]: "mirror (mirror x2) = x2"
by hipster_induct_schemes

lemma mirrorRev : "rev (flat_tree t) = flat_tree (mirror t)"
by hipster_induct_simp_metis

fun notNil :: "'a list \<Rightarrow> bool" where
  "notNil [] = False"
| "notNil _  = True"

fun rigthmost :: "'a binTree \<Rightarrow> 'a" where 
  "rigthmost (Leaf b)     = b"
| "rigthmost (Node b l r) = rigthmost r"

fun leftmost :: "'a binTree \<Rightarrow> 'a" where 
  "leftmost (Leaf b)     = b"
| "leftmost (Node b l r) = leftmost l"

lemma lemma_aa [thy_expl]: "hd (xs2 @ xs2) = hd xs2"
by (hipster_induct_schemes BinTree.notNil.simps BinTree.flat_tree.simps)

lemma lemma_ab [thy_expl]: "notNil (xs2 @ xs2) = notNil xs2"
by (hipster_induct_schemes BinTree.notNil.simps BinTree.flat_tree.simps)

(* did not discover or do we remov Nil_is_append_conv? *)
lemma notNApp [thy_expl]: "notNil (xs @ ys) = notNil (ys @ xs)"
by (hipster_induct_simp_metis notNil.elims Nil_is_append_conv)

lemma flatInhabited [thy_expl]: "flat_tree t \<noteq> []"
by hipster_induct_simp_metis

lemma unproved : "hd (flat_tree x) = leftmost x"
by hipster_induct_simp_metis

lemma sizeLen : "tree_size t = length (flat_tree t)"
by hipster_induct_simp_metis

datatype nTree = Stop | Inner nat nTree nTree

fun insertT :: "nat \<Rightarrow> nTree \<Rightarrow> nTree" where
  "insertT n Stop          = Inner n Stop Stop"
| "insertT n (Inner m l r) = (if n < m then Inner m (insertT n l) r
                                       else Inner m l (insertT n r))"

fun nHeight :: "nTree \<Rightarrow> nat" where
  "nHeight Stop          = 0"
| "nHeight (Inner _ l r) = 1 + max (nHeight l) (nHeight r)"

fun flatten :: "nTree \<Rightarrow> nat list" where
  "flatten Stop = []"
| "flatten (Inner n l r) = flatten l @ n # flatten r"

datatype 'a graph = GNode 'a "(('a graph) list)" (* coinduct ... *)

thm graph.induct


  declare [[show_types]]
  declare [[show_sorts]]
  declare [[show_consts]]

fun ack :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ack 0 n = n + 1"
| "ack m 0 = ack (m - 1) 1"
| "ack m n = ack (m - 1) (ack m (n - 1))"

fun ack2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ack2 m n 0 = m + n"
| "ack2 m 0 (Suc 0) = 0"
| "ack2 m 0 (Suc (Suc 0)) = 1"
| "ack2 m 0 p = m"
| "ack2 m n p = ack2 m (ack2 m (n - 1) p) (p - 1)"

end

