theory prop_51
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
  (*hipster butlast append *)
  theorem x0 :
    "(butlast (append xs (Cons2 x (Nil2)))) = xs"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
