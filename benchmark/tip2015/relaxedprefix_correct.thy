theory relaxedprefix_correct
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype It = A | B | C
  fun removeOne2 :: "It => (It list) list => (It list) list" where
  "removeOne2 x (nil) = nil"
  | "removeOne2 x (cons z x2) = cons (cons x z) (removeOne2 x x2)"
  fun removeOne :: "It list => (It list) list" where
  "removeOne (nil) = nil"
  | "removeOne (cons y xs) = cons xs (removeOne2 y (removeOne xs))"
  fun or2 :: "bool list => bool" where
  "or2 (nil) = False"
  | "or2 (cons True z) = True"
  | "or2 (cons False z) = or2 z"
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
  "isPrefix (nil) y = True"
  | "isPrefix (cons z x2) (nil) = False"
  | "isPrefix (cons z x2) (cons x3 x4) =
       (if eq z x3 then isPrefix x2 x4 else False)"
  fun spec2 :: "It list => (It list) list => bool list" where
  "spec2 ys (nil) = nil"
  | "spec2 ys (cons y z) = cons (isPrefix y ys) (spec2 ys z)"
  fun spec :: "It list => It list => bool" where
  "spec x y = or2 (spec2 y (cons x (removeOne x)))"
  fun isRelaxedPrefix :: "It list => It list => bool" where
  "isRelaxedPrefix (nil) y = True"
  | "isRelaxedPrefix (cons z (nil)) y = True"
  | "isRelaxedPrefix (cons z (cons x3 x4)) (nil) = False"
  | "isRelaxedPrefix (cons z (cons x3 x4)) (cons x5 x6) =
       (if eq z x5 then isRelaxedPrefix (cons x3 x4) x6 else
          isPrefix (cons x3 x4) (cons x5 x6))"
  theorem x0 :
    "!! (xs :: It list) (ys :: It list) .
       (isRelaxedPrefix xs ys) = (spec xs ys)"
    oops
end
