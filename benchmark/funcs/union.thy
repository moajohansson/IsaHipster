theory union
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/equal"
        "$HIPSTER_HOME/IsaHipster"

begin

datatype NList = NNil | NCons Nat NList

fun elemN :: "Nat => NList => bool" where
  "elemN x (NNil) = False"
| "elemN x (NCons z xs) = (if equal2 x z then True else elemN x xs)"

fun union :: "NList => NList => NList" where
  "union (NNil) y = y"
| "union (NCons z xs) y =
     (if elemN z y then union xs y else NCons z (union xs y))"

(*hipster union elemN equal2*)
lemma lemma_ad [thy_expl]: "union x1 NNil = x1"
by (hipster_induct_schemes union.simps elemN.simps equal2.simps)

(*hipster_cond elemN equal2 union elemN*)
lemma lemma_ae [thy_expl]: "elemN x9 z9 \<Longrightarrow> elemN x9 (union y9 z9) = True"
by (hipster_induct_schemes elemN.simps equal2.simps union.simps elemN.simps)

lemma lemma_af [thy_expl]: "elemN x1 z1 \<Longrightarrow> union (NCons x1 y1) (union z1 xa1) = union y1 (union z1 xa1)"
by (hipster_induct_schemes elemN.simps equal2.simps union.simps elemN.simps)

lemma lemma_ag [thy_expl]: "elemN x1 y1 \<Longrightarrow> union (NCons x1 NNil) (union y1 z1) = union y1 z1"
by (hipster_induct_schemes elemN.simps equal2.simps union.simps elemN.simps)

lemma unknown [thy_expl]: "union x x = x"
by (hipster_induct_schemes elemN.simps equal2.simps union.simps )

lemma unknown [thy_expl]: "elemN x (union y z) = elemN x (union z y)"
oops

lemma unknown [thy_expl]: "union (union x y) z = union x (union y z)"
oops

lemma unknown [thy_expl]: "union x (union x y) = union x y"
oops

lemma unknown [thy_expl]: "union x (union y x) = union y x"
oops

lemma unknown [thy_expl]: "union x (NCons y x) = NCons y x"
oops

lemma unknown [thy_expl]: "union (union x y) x = union y x"
oops

lemma unknown [thy_expl]: "union (union x y) y = union x y"
oops

lemma unknown [thy_expl]: "union (union x y) (union x z) =
union y (union x z)"
oops

lemma unknown [thy_expl]: "union (union x y) (union y z) =
union x (union y z)"
oops

lemma unknown [thy_expl]: "union (union x y) (union z x) =
union y (union z x)"
oops

lemma unknown [thy_expl]: "union (union x y) (union z y) =
union x (union z y)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons z x) = union y (NCons z x)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons z y) = union x (NCons z y)"
oops

lemma unknown [thy_expl]: "union (NCons x y) (union z y) =
union (NCons x z) (union z y)"
oops

lemma unknown [thy_expl]: "union (NCons x y) (union y z) =
union (NCons x z) (union y z)"
oops

lemma unknown [thy_expl]: "elemN (S x) (union y z) = elemN (S x) (union z y)"
oops

lemma unknown [thy_expl]: "elemN Z (union x y) = elemN Z (union y x)"
oops

lemma unknown [thy_expl]: "union (union x y) (union x y) = union x y"
oops

lemma unknown [thy_expl]: "union (union x y) (union y x) = union y x"
oops

lemma unknown [thy_expl]: "union (NCons x y) (NCons x y) = NCons x y"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) y = union (NCons x y) y"
oops

lemma unknown [thy_expl]: "union x (NCons Z x) = NCons Z x"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (union y z) =
union (NCons x y) (union y z)"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (union y z) =
union (NCons x z) (union y z)"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (NCons y z) = union (NCons x z) (NCons y z)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons Z x) = union y (NCons Z x)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons Z y) = union x (NCons Z y)"
oops

lemma unknown [thy_expl]: "union (NCons Z x) (union y x) =
union (NCons Z y) (union y x)"
oops

lemma unknown [thy_expl]: "union (NCons Z x) (union x y) =
union (NCons Z y) (union x y)"
oops

lemma unknown [thy_expl]: "elemN (S Z) (union x y) = elemN (S Z) (union y x)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) x = union (NCons Z x) x"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (NCons Z y) = union (NCons x y) (NCons Z y)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) (union x y) =
union (NCons Z x) (union x y)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) (union x y) =
union (NCons Z y) (union x y)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) (NCons x y) = union (NCons Z y) (NCons x y)"
oops

lemma unknown [thy_expl]: "union (NCons Z x) (NCons Z x) = NCons Z x"
oops

lemma unknown [thy_expl]: "elemN x y \<Longrightarrow> union (NCons x y) y = y"
oops

lemma unknown [thy_expl]: "elemN x y \<Longrightarrow>
union (NCons x y) (union y z) = union y z"
oops

lemma unknown [thy_expl]: "elemN x y \<Longrightarrow>
union (NCons x y) (union z y) = union z y"
oops

lemma unknown [thy_expl]: "elemN x y \<Longrightarrow> union (NCons x y) (NCons z y) = NCons z y"
oops

lemma unknown [thy_expl]: "elemN x z \<Longrightarrow>
union (NCons x y) (union z y) = union z y"
oops

lemma unknown [thy_expl]: "elemN x z \<Longrightarrow>
union (NCons x y) (union y z) = union y z"
oops

lemma unknown [thy_expl]: "elemN x y \<Longrightarrow> union (NCons x y) (NCons Z y) = NCons Z y"
oops

hipster_cond equal2 elemN union equal2

lemma unknown [thy_expl]: "union x x = x"
by (hipster_induct_schemes union.simps elemN.simps equal2.simps Nat.exhaust NList.exhaust)


lemma unknown [thy_expl]: "elemN x (union y z) = elemN x (union z y)"
oops

lemma unknown [thy_expl]: "union (union x y) z = union x (union y z)"
oops

lemma unknown [thy_expl]: "union x (union x y) = union x y"
oops

lemma unknown [thy_expl]: "union x (union y x) = union y x"
oops

lemma unknown [thy_expl]: "union x (NCons y x) = NCons y x"
oops

lemma unknown [thy_expl]: "union (union x y) x = union y x"
oops

lemma unknown [thy_expl]: "union (union x y) y = union x y"
oops

lemma unknown [thy_expl]: "union (union x y) (union x z) = union y (union x z)"
oops

lemma unknown [thy_expl]: "union (union x y) (union y z) = union x (union y z)"
oops

lemma unknown [thy_expl]: "union (union x y) (union z x) = union y (union z x)"
oops

lemma unknown [thy_expl]: "union (union x y) (union z y) = union x (union z y)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons z x) = union y (NCons z x)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons z y) = union x (NCons z y)"
oops

lemma unknown [thy_expl]: "union (NCons x y) (union z y) = union (NCons x z) (union z y)"
oops

lemma unknown [thy_expl]: "union (NCons x y) (union y z) = union (NCons x z) (union y z)"
oops

lemma unknown [thy_expl]: "elemN (S x) (union y z) = elemN (S x) (union z y)"
oops

lemma unknown [thy_expl]: "elemN Z (union x y) = elemN Z (union y x)"
oops

lemma unknown [thy_expl]: "union (union x y) (union x y) = union x y"
oops

lemma unknown [thy_expl]: "union (union x y) (union y x) = union y x"
oops

lemma unknown [thy_expl]: "union (NCons x y) (NCons x y) = NCons x y"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) y = union (NCons x y) y"
oops

lemma unknown [thy_expl]: "union x (NCons Z x) = NCons Z x"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (union y z) = union (NCons x y) (union y z)"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (union y z) = union (NCons x z) (union y z)"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (NCons y z) = union (NCons x z) (NCons y z)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons Z x) = union y (NCons Z x)"
oops

lemma unknown [thy_expl]: "union (union x y) (NCons Z y) = union x (NCons Z y)"
oops

lemma unknown [thy_expl]: "union (NCons Z x) (union y x) = union (NCons Z y) (union y x)"
oops

lemma unknown [thy_expl]: "union (NCons Z x) (union x y) = union (NCons Z y) (union x y)"
oops

lemma unknown [thy_expl]: "elemN (S Z) (union x y) = elemN (S Z) (union y x)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) x = union (NCons Z x) x"
oops

lemma unknown [thy_expl]: "union (NCons x NNil) (NCons Z y) = union (NCons x y) (NCons Z y)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) (union x y) = union (NCons Z x) (union x y)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) (union x y) = union (NCons Z y) (union x y)"
oops

lemma unknown [thy_expl]: "union (NCons Z NNil) (NCons x y) = union (NCons Z y) (NCons x y)"
oops

lemma unknown [thy_expl]: "union (NCons Z x) (NCons Z x) = NCons Z x"
oops

lemma t: "\<not> equal2 u v \<Longrightarrow> elem u (Cons2 v x) = elem u x"
oops

lemma u : "union x (NCons a x) = NCons a x"
apply(induction x)
apply simp
oops

lemma unknown [thy_expl]: "union x x = x"
apply(induction x)
apply(simp_all)
apply rule
apply rule
apply(hipster_induct_schemes simps list.exhaust Nat.exhaust equal2.simps elem.simps lemma_a )
oops

end

