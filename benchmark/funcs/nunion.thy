theory nunion
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

lemma xu : "union (NCons y ys) (NCons y ys) = NCons y (union ys ys)"
apply(induction ys)
apply simp+
oops

(*lemma xw : "elemN x ys \<Longrightarrow> elemN x (union xs ys)"
by (hipster_induct_schemes elemN.simps union.simps equal2.simps)*)

(*lemma xz : "elemN x (union (NCons x xs) ys)"
by (hipster_induct_schemes xw elemN.simps union.simps equal2.simps)*)

lemma xy : "elemN x xs \<Longrightarrow> elemN x (union xs ys)"
by (hipster_induct_schemes  elemN.simps union.simps equal2.simps)

lemma xv: "\<And>xs. (ALL elemN x xs. elemN x ys \<Longrightarrow> union xs ys = ys)"
apply(induction)
apply simp_all
oops

end
