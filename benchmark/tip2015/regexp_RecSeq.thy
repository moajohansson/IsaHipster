theory regexp_RecSeq
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
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
  fun consfst :: "'a => ((('a list), 'b) Pair2) list =>
                  ((('a list), 'b) Pair2) list" where
  "consfst x (nil) = nil"
  | "consfst x (cons (Pair xs y2) ys) =
       cons (Pair (cons x xs) y2) (consfst x ys)"
  fun split :: "'a list => ((('a list), ('a list)) Pair2) list" where
  "split (nil) = cons (Pair (nil) (nil)) (nil)"
  | "split (cons y s) =
       cons (Pair (nil) (cons y s)) (consfst y (split s))"
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
  "recognise x (nil) = eps x"
  | "recognise x (cons z xs) = recognise (step x z) xs"
  fun recognisePair :: "R => R =>
                      (((A list), (A list)) Pair2) list => bool" where
  "recognisePair x y (nil) = False"
  | "recognisePair x y (cons (Pair s1 s2) xs) =
       or2
         (and2 (recognise x s1) (recognise y s2)) (recognisePair x y xs)"
  theorem x0 :
    "!! (p :: R) (q :: R) (s :: A list) .
       (recognise (Seq p q) s) = (recognisePair p q (split s))"
    oops
end
