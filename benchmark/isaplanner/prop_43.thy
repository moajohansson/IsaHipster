theory prop_43
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (Nil2) = Nil2"
  | "takeWhile x (Cons2 z xs) =
       (if x z then Cons2 z (takeWhile x xs) else Nil2)"
  fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (Nil2) = Nil2"
  | "dropWhile x (Cons2 z xs) =
       (if x z then dropWhile x xs else Cons2 z xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster takeWhile dropWhile append *)
  theorem x0 :
    "(append (takeWhile p xs) (dropWhile p xs)) = xs"
    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
