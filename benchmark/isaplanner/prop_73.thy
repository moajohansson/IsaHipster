theory prop_73
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter x (Nil2) = Nil2"
  | "filter x (Cons2 z xs) =
       (if x z then Cons2 z (filter x xs) else filter x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster filter append rev *)
  theorem x0 :
    "(rev (filter p xs)) = (filter p (rev xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
