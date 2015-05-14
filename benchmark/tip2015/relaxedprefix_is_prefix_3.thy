theory relaxedprefix_is_prefix_3
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
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
  "isPrefix (nil) y = True"
  | "isPrefix (cons z x2) (nil) = False"
  | "isPrefix (cons z x2) (cons x3 x4) =
       (if eq z x3 then isPrefix x2 x4 else False)"
  fun isRelaxedPrefix :: "It list => It list => bool" where
  "isRelaxedPrefix (nil) y = True"
  | "isRelaxedPrefix (cons z (nil)) y = True"
  | "isRelaxedPrefix (cons z (cons x3 x4)) (nil) = False"
  | "isRelaxedPrefix (cons z (cons x3 x4)) (cons x5 x6) =
       (if eq z x5 then isRelaxedPrefix (cons x3 x4) x6 else
          isPrefix (cons x3 x4) (cons x5 x6))"
  fun append :: "It list => It list => It list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (x :: It) (xs :: It list) (ys :: It list) .
       isRelaxedPrefix (append xs (cons x (nil))) (append xs ys)"
    oops
end
