theory prop_31
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (nil) y = y"
  | "qrev (cons z xs) y = qrev xs (cons z y)"
  theorem x0 :
    "!! (x :: 'a list) . (qrev (qrev x (nil)) (nil)) = x"
    oops
end
