theory mccarthy91_M1
imports Main
        "../../IsaHipster"
begin

function m :: "int => int" where
"m x = (if x > 100 then x - 10 else m (m (x + 11)))"
by pat_completeness auto

(*hipster m *)

theorem x0 :
  "!! (n :: int) . (n <= 100) ==> ((m n) = 91)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
