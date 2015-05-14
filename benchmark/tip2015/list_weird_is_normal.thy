theory list_weird_is_normal
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun weirdconcat :: "('a list) list => 'a list" where
  "weirdconcat (nil) = nil"
  | "weirdconcat (cons (nil) xss) = weirdconcat xss"
  | "weirdconcat (cons (cons z xs) xss) =
       cons z (weirdconcat (cons xs xss))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun concat2 :: "('a list) list => 'a list" where
  "concat2 (nil) = nil"
  | "concat2 (cons xs xss) = append xs (concat2 xss)"
  theorem x0 :
    "!! (x :: ('a list) list) . (concat2 x) = (weirdconcat x)"
    oops
end
