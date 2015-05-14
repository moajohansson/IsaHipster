theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a 'b Pair2 = Pair "'a" "'b"
  fun zip :: "'a list => 'b list => ('a 'b Pair2) list" where
  "zip (nil) y = nil"
  | "zip (cons z x2) (nil) = nil"
  | "zip (cons z x2) (cons x3 x4) = cons (Pair z x3) (zip x2 x4)"
  theorem x0 :
    "!! (xs :: 'b list) . (zip (nil) xs) = (nil)"
    oops
end
