theory regexp_RecAtom
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype A = X | Y

datatype R
  = Nil2 | Eps | Atom "A" | Plus "R" "R" | Seq "R" "R" | Star "R"

fun seq :: "R => R => R" where
"seq x y =
   case x of
     | other =>
         case y of
           | other =>
               case x of
                 | other =>
                     case y of
                       | other => Seq x y
                       | Eps => x
                     end
                 | Eps => y
               end
           | Nil2 => y
         end
     | Nil2 => x
   end"

fun plus :: "R => R => R" where
"plus x y =
   case x of
     | other =>
         case y of
           | other => Plus x y
           | Nil2 => x
         end
     | Nil2 => y
   end"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun eqA :: "A => A => bool" where
"eqA (X) y = False"
| "eqA (Y) (X) = False"
| "eqA (Y) (Y) = True"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun eps :: "R => bool" where
"eps x =
   case x of
     | other => False
     | Eps => True
     | Plus p q => or2 (eps p) (eps q)
     | Seq p2 q2 => and2 (eps p2) (eps q2)
     | Star y => True
   end"

fun epsR :: "R => R" where
"epsR x = (if eps x then Eps else Nil2)"

fun step :: "R => A => R" where
"step x y =
   case x of
     | other => Nil2
     | Atom a => (if eqA a y then Eps else Nil2)
     | Plus p q => plus (step p y) (step q y)
     | Seq p2 q2 =>
         plus (seq (step p2 y) q2) (seq (epsR p2) (step q2 y))
     | Star p3 => seq (step p3 y) x
   end"

fun recognise :: "R => A list => bool" where
"recognise x (Nil2) = eps x"
| "recognise x (Cons2 z xs) = recognise (step x z) xs"

fun eqList :: "A list => A list => bool" where
"eqList (Nil2) (Nil2) = True"
| "eqList (Nil2) (Cons2 z x2) = False"
| "eqList (Cons2 x3 xs) (Nil2) = False"
| "eqList (Cons2 x3 xs) (Cons2 y2 ys) =
     and2 (eqA x3 y2) (eqList xs ys)"

(*hipster seq plus or2 eqA and2 eps epsR step recognise eqList *)

theorem x0 :
  "!! (a :: A) (s :: A list) .
     (recognise (Atom a) s) = (eqList s (Cons2 a (Nil2)))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
