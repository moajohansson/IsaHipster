theory list_weird_concat_fmap_bind
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun weirdconcat :: "('a list) list => 'a list" where
  "weirdconcat (Nil2) = Nil2"
  | "weirdconcat (Cons2 (Nil2) xss) = weirdconcat xss"
  | "weirdconcat (Cons2 (Cons2 z xs) xss) =
       Cons2 z (weirdconcat (Cons2 xs xss))"
  fun fmap :: "('a => 'b) => 'a list => 'b list" where
  "fmap x (Nil2) = Nil2"
  | "fmap x (Cons2 z xs) = Cons2 (x z) (fmap x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun bind :: "'a list => ('a => 'b list) => 'b list" where
  "bind (Nil2) y = Nil2"
  | "bind (Cons2 z xs) y = append (y z) (bind xs y)"
  (*hipster weirdconcat fmap append bind *)
  theorem x0 :
    "(weirdconcat (fmap f xs)) = (bind xs f)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
