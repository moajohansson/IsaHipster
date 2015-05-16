theory relaxedprefix_correct
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype It = A | B | C
  fun removeOne2 :: "It => (It list) list => (It list) list" where
  "removeOne2 x (Nil2) = Nil2"
  | "removeOne2 x (Cons2 z x2) = Cons2 (Cons2 x z) (removeOne2 x x2)"
  fun removeOne :: "It list => (It list) list" where
  "removeOne (Nil2) = Nil2"
  | "removeOne (Cons2 y xs) = Cons2 xs (removeOne2 y (removeOne xs))"
  fun or2 :: "bool list => bool" where
  "or2 (Nil2) = False"
  | "or2 (Cons2 True z) = True"
  | "or2 (Cons2 False z) = or2 z"
  fun eq :: "It => It => bool" where
  "eq (A) y =
     case y of
       | other => False
       | A => True
     end"
  | "eq (B) y =
       case y of
         | other => False
         | B => True
       end"
  | "eq (C) y =
       case y of
         | other => False
         | C => True
       end"
  fun isPrefix :: "It list => It list => bool" where
  "isPrefix (Nil2) y = True"
  | "isPrefix (Cons2 z x2) (Nil2) = False"
  | "isPrefix (Cons2 z x2) (Cons2 x3 x4) =
       (if eq z x3 then isPrefix x2 x4 else False)"
  fun spec2 :: "It list => (It list) list => bool list" where
  "spec2 ys (Nil2) = Nil2"
  | "spec2 ys (Cons2 y z) = Cons2 (isPrefix y ys) (spec2 ys z)"
  fun spec :: "It list => It list => bool" where
  "spec x y = or2 (spec2 y (Cons2 x (removeOne x)))"
  fun isRelaxedPrefix :: "It list => It list => bool" where
  "isRelaxedPrefix (Nil2) y = True"
  | "isRelaxedPrefix (Cons2 z (Nil2)) y = True"
  | "isRelaxedPrefix (Cons2 z (Cons2 x3 x4)) (Nil2) = False"
  | "isRelaxedPrefix (Cons2 z (Cons2 x3 x4)) (Cons2 x5 x6) =
       (if eq z x5 then isRelaxedPrefix (Cons2 x3 x4) x6 else
          isPrefix (Cons2 x3 x4) (Cons2 x5 x6))"
  (*hipster removeOne2
            removeOne
            or2
            eq
            isPrefix
            spec2
            spec
            isRelaxedPrefix *)
  theorem x0 :
    "(isRelaxedPrefix xs ys) = (spec xs ys)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
