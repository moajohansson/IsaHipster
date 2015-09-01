theory Sorted
imports Main
        "$HIPSTER_HOME/IsaHipster"

begin

  datatype 'a list = Nil | Cons "'a" "'a list"
  datatype Nat = Z | S "Nat"

  fun le :: "Nat => Nat => bool" where
    "le Z y = True"
  | "le (S x) Z = False"
  | "le (S x) (S x2) = le x x2"

  fun sorted :: "Nat list => bool" where
    "sorted Nil = True"
  | "sorted (Cons y Nil) = True"
  | "sorted (Cons y (Cons y2 ys)) =
       (if le y y2 then sorted (Cons y2 ys) else False)"

  fun insert :: "Nat => Nat list => Nat list" where
    "insert x Nil = Cons x Nil"
  | "insert x (Cons z xs) =
       (if le x z then Cons x (Cons z xs) else Cons z (insert x xs))"

  fun sort :: "Nat list => Nat list" where
  "sort Nil = Nil"
  | "sort (Cons y xs) = insert y (sort xs)"

(* First: explore the most simple function, ie: that which is defined in terms of itself alone *)
(*hipster le*)
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

(* We might need conditionals: we explore those with up to two conjuncts in the premise *)
(*hipster_cond le*)
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_af [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

(* We proceed on to explore other functions in the theory, and we find some properties we
    cannot prove yet *)
(*hipster sorted insert le*)
lemma lemma_ag [thy_expl]: "insert Z (insert x19 y19) = insert x19 (insert Z y19)"
by (hipster_induct_schemes sorted.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma lemma_ah [thy_expl]: "sorted (insert Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma unknown [thy_expl]: "insert x (insert y z) = insert y (insert x z)"
oops

lemma unknown [thy_expl]: "sorted (insert x y) = sorted y"
oops

(* Neither when considering conditionals with the predicate _sorted_ *)
(*hipster_cond sorted insert le *)
lemma unknown [thy_expl]: "insert x (insert y z) = insert y (insert x z)"
oops

lemma unknown [thy_expl]: "sorted (insert x y) = sorted y"
oops

lemma unknown [thy_expl]: "sorted y \<Longrightarrow> sorted (insert x y) = True"
oops


(* So we might think about exploring the negation of some predicate, namely of that which
    defines branching in our sorting functions. Right now, we need to define it separately
    for exploration purposes *)
fun notle:: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "notle x y = (\<not> le x y)"

(* And we finally explore conditional properties for it *)
(*hipster_cond notle*)
lemma lemma_ai [thy_expl]: "notle (S x2) y2 = le y2 x2"
by (hipster_induct_schemes notle.simps Nat.exhaust)

lemma lemma_aj [thy_expl]: "notle x2 y2 \<Longrightarrow> notle x2 Z = True"
by (hipster_induct_schemes notle.simps Nat.exhaust)


(* If we now revisit one of the lemmas discovered about _sorted_ and _insert_, we will be able
    to prove after prior modification of the options: using full_types in metis and increasing
    the timeout for proof search (namely that for metis) *)
setup{* Hip_Tac_Ops.toggle_full_types @{context} ;*}
setup{* Hip_Tac_Ops.set_metis_to @{context} 3500;*}

(*hipster_cond sorted (*sort*) insert le notle*)
lemma lemma_ak [thy_expl]: "insert x30 (insert y30 z30) = insert y30 (insert x30 z30)"
by (hipster_induct_schemes sorted.simps insert.simps le.simps notle.simps list.exhaust Nat.exhaust)

lemma lemma_al [thy_expl]: "sorted y31 \<Longrightarrow> sorted (insert x31 y31) = True"
by (hipster_induct_schemes sorted.simps insert.simps le.simps notle.simps list.exhaust Nat.exhaust)

lemma unknown [thy_expl]: "sorted (insert x y) = sorted y"
oops


(* We can finally immediately prove our target theorem! *)
  theorem x0 :
    "sorted (sort xs)"
    by hipster_induct_schemes

end
