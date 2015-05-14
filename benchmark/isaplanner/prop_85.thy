theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a 'b Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => ('a 'b Pair2) list" where
  "zip (nil) y = nil"
  | "zip (cons z x2) (nil) = nil"
  | "zip (cons z x2) (cons x3 x4) = cons (Pair z x3) (zip x2 x4)"
  fun len :: "'a list => Nat" where
  "len (nil) = Z"
  | "len (cons y xs) = S (len xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (nil) = nil"
  | "rev (cons y xs) = append (rev xs) (cons y (nil))"
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'b list) .
       ((len xs) = (len ys)) ==>
         ((zip (rev xs) (rev ys)) = (rev (zip xs ys)))"
    oops
end
