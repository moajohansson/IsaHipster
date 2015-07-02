theory prop_36
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (Nil2) = Nil2"
  | "takeWhile x (Cons2 z xs) =
       (if x z then Cons2 z (takeWhile x xs) else Nil2)"
  (*hipster takeWhile *)
  theorem x0 :
    "(takeWhile (% (x :: 'a) => True) xs) = xs"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
