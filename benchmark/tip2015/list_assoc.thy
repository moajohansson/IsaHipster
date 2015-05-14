theory list_assoc
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun bind :: "'a list => ('a => 'b list) => 'b list" where
  "bind (nil) y = nil"
  | "bind (cons z xs) y = append (y z) (bind xs y)"
  theorem x0 :
    "!! (m :: 'a list) (f :: ('a => 'b list)) (g :: ('b => 'c list)) .
       (bind (bind m f) g) = (bind m (% (x :: 'a) => bind (f x) g))"
    oops
end
