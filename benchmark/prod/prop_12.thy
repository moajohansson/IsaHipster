theory prop_12
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
  | "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  hipster qrev append rev
  theorem x0 :
    "!! (x :: 'a list) (y :: 'a list) .
       (qrev x y) = (append (rev x) y)"
    oops
end
