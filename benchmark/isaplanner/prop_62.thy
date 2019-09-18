theory prop_62
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun null :: "'a list => bool" where
  "null (Nil2) = True"
  | "null (Cons2 y z) = False"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  (*hipster null last *)
  theorem x0 :
    "(~ (null xs)) ==> ((last (Cons2 x xs)) = (last xs))"
    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
