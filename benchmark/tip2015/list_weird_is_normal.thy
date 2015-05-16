theory list_weird_is_normal
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun weirdconcat :: "('a list) list => 'a list" where
  "weirdconcat (Nil2) = Nil2"
  | "weirdconcat (Cons2 (Nil2) xss) = weirdconcat xss"
  | "weirdconcat (Cons2 (Cons2 z xs) xss) =
       Cons2 z (weirdconcat (Cons2 xs xss))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun concat2 :: "('a list) list => 'a list" where
  "concat2 (Nil2) = Nil2"
  | "concat2 (Cons2 xs xss) = append xs (concat2 xss)"
  (*hipster weirdconcat append concat2 *)
  theorem x0 :
    "(concat2 x) = (weirdconcat x)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
