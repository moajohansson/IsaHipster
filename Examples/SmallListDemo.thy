theory SmallListDemo
imports "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

fun app :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" 
where 
  "app Emp xs = xs"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a Lst \<Rightarrow> 'a Lst"
where 
  "rev Emp = Emp"
| "rev (Cons x xs) = app (rev xs) (Cons x Emp)"

theorem rev_rev : "rev(rev xs) = xs "
apply (induct xs)
apply (simp+)
apply (tactic {* Hipster_Explore.explore_goal @{context} ["SmallListDemo.rev", "SmallListDemo.app"] *})

end
