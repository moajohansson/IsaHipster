theory prop_35
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (Nil2) = Nil2"
  | "dropWhile x (Cons2 z xs) =
       (if x z then dropWhile x xs else Cons2 z xs)"
  (*hipster dropWhile *)
  theorem x0 :
    "(dropWhile (% (x :: 'a) => False) xs) = xs"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
