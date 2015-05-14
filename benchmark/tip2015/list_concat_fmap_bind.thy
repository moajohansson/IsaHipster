theory list_concat_fmap_bind
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun fmap :: "('a => 'b) => 'a list => 'b list" where
  "fmap x (nil) = nil"
  | "fmap x (cons z xs) = cons (x z) (fmap x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun bind :: "'a list => ('a => 'b list) => 'b list" where
  "bind (nil) y = nil"
  | "bind (cons z xs) y = append (y z) (bind xs y)"
  fun concat2 :: "('a list) list => 'a list" where
  "concat2 (nil) = nil"
  | "concat2 (cons xs xss) = append xs (concat2 xss)"
  theorem x0 :
    "!! (f :: ('a => 'b list)) (xs :: 'a list) .
       (concat2 (fmap f xs)) = (bind xs f)"
    oops
end
