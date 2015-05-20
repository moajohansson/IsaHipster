theory relaxedprefix_is_prefix_2
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype It = A | B | C

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

fun isRelaxedPrefix :: "It list => It list => bool" where
"isRelaxedPrefix (Nil2) y = True"
| "isRelaxedPrefix (Cons2 z (Nil2)) y = True"
| "isRelaxedPrefix (Cons2 z (Cons2 x3 x4)) (Nil2) = False"
| "isRelaxedPrefix (Cons2 z (Cons2 x3 x4)) (Cons2 x5 x6) =
     (if eq z x5 then isRelaxedPrefix (Cons2 x3 x4) x6 else
        isPrefix (Cons2 x3 x4) (Cons2 x5 x6))"

fun append :: "It list => It list => It list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

(*hipster eq isPrefix isRelaxedPrefix append *)

theorem x0 :
  "!! (x :: It) (xs :: It list) (ys :: It list) (zs :: It list) .
     isRelaxedPrefix
       (append (append xs (Cons2 x (Nil2))) ys)
       (append (append xs ys) zs)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
