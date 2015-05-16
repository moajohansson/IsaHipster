theory prop_27
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
  | "qrev (Cons2 z xs) y = qrev xs (cons2 z y)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = nil2"
  | "rev (Cons2 y xs) = append (rev xs) (cons2 y (Nil2))"
  hipster qrev append rev
  theorem x0 :
    "!! (x :: 'a list) . (rev x) = (qrev x (Nil2))"
    oops
end
