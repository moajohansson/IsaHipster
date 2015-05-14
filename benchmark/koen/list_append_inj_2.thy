theory list_append_inj_2
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'a list) (zs :: 'a list) .
       ((append xs ys) = (append xs zs)) ==> (ys = zs)"
    oops
end
