theory GeneralisedErr
imports Main
        "$HIPSTER_HOME/IsaHipster"

begin

datatype Nat = Z | S Nat

datatype 'a List = Nil | Cons 'a "'a List"

fun app :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "app Nil         ts = ts"
| "app (Cons r rs) ts = Cons r (app rs ts)"

fun rotate :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "rotate Z     xs          = xs"
| "rotate (S n) (Cons x xs) = rotate n (app xs (Cons x Nil))"
| "rotate n     Nil         = Nil"

hipster rotate

lemma problem : "rotate (S Z) (rotate x y) = rotate (S x) y"
apply(induction x y rule: rotate.induct)
apply simp_all

done


