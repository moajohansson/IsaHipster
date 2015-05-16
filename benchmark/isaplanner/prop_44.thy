theory prop_44
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
  | "zip (Cons2 z x2) (Nil2) = Nil2"
  | "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip x2 x4)"
  fun zipConcat :: "'a => 'a list => 'b list =>
                    (('a, 'b) Pair2) list" where
  "zipConcat x y (Nil2) = Nil2"
  | "zipConcat x y (Cons2 y2 ys) = Cons2 (Pair x y2) (zip y ys)"
  (*hipster zip zipConcat *)
  theorem x0 :
    "(zip (Cons2 x xs) ys) = (zipConcat x xs ys)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
