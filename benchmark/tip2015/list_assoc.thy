theory list_assoc
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun bind :: "'a list => ('a => 'b list) => 'b list" where
  "bind (Nil2) y = Nil2"
  | "bind (Cons2 z xs) y = append (y z) (bind xs y)"
  (*hipster append bind *)
  theorem x0 :
    "(bind (bind m f) g) = (bind m (% (x :: 'a) => bind (f x) g))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
