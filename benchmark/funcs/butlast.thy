theory butlast
imports Main
        "../data/list"
        "../funcs/append"
        "$HIPSTER_HOME/IsaHipster"

begin

fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
| "butlast (Cons2 y (Nil2)) = Nil2"
| "butlast (Cons2 y (Cons2 x2 x3)) = Cons2 y (butlast (Cons2 x2 x3))"

(*hipster butlast append*)

lemma unknown []: "butlast.butlast (append.append x x) = append.append x (butlast.butlast x)"
oops

lemma xa : " append.append (Cons2 x Nil2) y = Cons2 x y "
by (tactic {* Tactic_Data.routine_tac @{context} *})
lemma xb : " append.append (Cons2 x Nil2) (append.append y z) = Cons2 x (append.append y z) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma xc : " append.append (Cons2 x Nil2) (Cons2 y z) = Cons2 x (Cons2 y z) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma xd : " append.append (Cons2 x Nil2) (append.append y y) = Cons2 x (append.append y y) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma xe : " append.append (Cons2 x Nil2) (Cons2 x y) = Cons2 x (Cons2 x y) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma xf : " append.append (Cons2 x Nil2) (butlast.butlast y) = Cons2 x (butlast.butlast y) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma xg : " append.append (Cons2 x Nil2) (Cons2 y Nil2) = Cons2 x (Cons2 y Nil2) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma xh : " append.append (Cons2 x Nil2) (Cons2 x Nil2) = Cons2 x (Cons2 x Nil2) "
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma unknown []: "butlast.butlast (append.append x x) = append.append x (butlast.butlast x)"
apply(hipster_induct_schemes butlast.simps append.simps list.exhaust)
end

