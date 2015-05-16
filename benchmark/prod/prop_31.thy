theory prop_31
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
  | "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"
  hipster qrev
  theorem x0 :
    "!! (x :: 'a list) . (qrev (qrev x (Nil2)) (Nil2)) = x"
    oops
end
