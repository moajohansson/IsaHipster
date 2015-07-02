theory heap_deleteMinimum
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype 'a Maybe = Nothing | Just "'a"

datatype Heap = Node "Heap" "Nat" "Heap" | Nil3

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun listDeleteMinimum :: "Nat list => (Nat list) Maybe" where
"listDeleteMinimum (Nil2) = Nothing"
| "listDeleteMinimum (Cons2 y xs) = Just xs"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun merge :: "Heap => Heap => Heap" where
"merge (Node z x2 x3) (Node x4 x5 x6) =
   (if le x2 x5 then Node (merge x3 (Node x4 x5 x6)) x2 z else
      Node (merge (Node z x2 x3) x6) x5 x4)"
| "merge (Node z x2 x3) (Nil3) = Node z x2 x3"
| "merge (Nil3) y = y"

fun toList :: "Nat => Heap => Nat list" where
"toList (Z) y = Nil2"
| "toList (S z) (Node x2 x3 x4) =
     Cons2 x3 (toList z (merge x2 x4))"
| "toList (S z) (Nil3) = Nil2"

fun heapSize :: "Heap => Nat" where
"heapSize (Node l y r) = S (plus (heapSize l) (heapSize r))"
| "heapSize (Nil3) = Z"

fun toList2 :: "Heap => Nat list" where
"toList2 x = toList (heapSize x) x"

fun maybeToList :: "Heap Maybe => (Nat list) Maybe" where
"maybeToList (Nothing) = Nothing"
| "maybeToList (Just y) = Just (toList2 y)"

fun deleteMinimum :: "Heap => Heap Maybe" where
"deleteMinimum (Node l y r) = Just (merge l r)"
| "deleteMinimum (Nil3) = Nothing"

(*hipster plus
          listDeleteMinimum
          le
          merge
          toList
          heapSize
          toList2
          maybeToList
          deleteMinimum *)

(*hipster plus le*)
lemma lemma_a [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_aa [thy_expl]: "plus (plus x1 y1) z1 =
plus x1 (plus y1 z1)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ab [thy_expl]: "plus x2 (S y2) = S (plus x2 y2)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ac [thy_expl]: "plus x1 (plus y1 x1) = plus y1 (plus x1 x1)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ad [thy_expl]: "plus x2 (plus y2 y2) = plus y2 (plus y2 x2)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ae [thy_expl]: "plus x2 (S y2) = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_af [thy_expl]: "plus (S x2) y2 = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ag [thy_expl]: "plus (plus x2 y2) (plus x2 z2) = plus (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) (plus z2 x2) = plus (plus z2 x2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_ai [thy_expl]: "plus (plus x1 x1) (plus y1 z1) =plus (plus x1 y1) (plus x1 z1)"
by (hipster_induct_schemes plus.simps le.simps)

lemma lemma_aj [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes plus.simps le.simps)

(*hipster le*)
lemma lemma_ak [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_al [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_am [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)


lemma lemma_an [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ao [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ap [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_trans [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

(*hipster heapSize plus*)

(*hipster le plus heapSize*)
lemma lemma_aq [thy_expl]: "le x2 (plus x2 y2) = True"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_ar [thy_expl]: "le (plus x2 y2) x2 = le y2 Z"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_as [thy_expl]: "le (plus x1 y1) (plus x1 z1) = le y1 z1"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps Nat.exhaust)

lemma lemma_at [thy_expl]: "le (plus x1 y1) (plus y1 z1) = le x1 z1"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_au [thy_expl]: "le (plus x2 y2) (S y2) = le (plus x2 z2) (S z2)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_av [thy_expl]: "le (plus x1 y1) (S x1) = le (plus z1 y1) (S z1)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_aw [thy_expl]: "le (plus x1 x1) (plus y1 y1) = le x1 y1"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_ax [thy_expl]: "le (S x2) (plus x2 y2) = le (S z2) (plus z2 y2)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_ay [thy_expl]: "le (S x1) (plus y1 x1) = le (S z1) (plus y1 z1)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_az [thy_expl]: "le (S x1) (plus y1 x1) = le (S z1) (plus z1 y1)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_ba [thy_expl]: "le x2 (S Z) = le (plus x2 y2) (S y2)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_bb [thy_expl]: "le (S Z) x2 = le (S y2) (plus x2 y2)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_bc [thy_expl]: "le (plus x2 x2) (S Z) = le x2 Z"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

lemma lemma_bd [thy_expl]: "le (S Z) (plus x2 x2) = le (S y2) (plus x2 y2)"
by (hipster_induct_schemes le.simps plus.simps heapSize.simps)

hipster toList toList2 maybeToList

hipster merge

theorem x0 :
  "!! (h :: Heap) .
     (listDeleteMinimum (toList2 h)) = (maybeToList (deleteMinimum h))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
