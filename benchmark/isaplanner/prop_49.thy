theory prop_49
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
  | "butlast (Cons2 y (Nil2)) = Nil2"
  | "butlast (Cons2 y (Cons2 x2 x3)) =
       Cons2 y (butlast (Cons2 x2 x3))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (Nil2) = butlast x"
  | "butlastConcat x (Cons2 z x2) = append x (butlast (Cons2 z x2))"
  (*hipster butlast append butlastConcat *)

  theorem x0 :
    "(butlast (append xs ys)) = (butlastConcat xs ys)"
    apply(hipster_induct_schemes append.simps butlastConcat.simps butlast.simps list.exhaust)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
