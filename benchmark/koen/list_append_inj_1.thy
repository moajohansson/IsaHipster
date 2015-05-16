theory list_append_inj_1
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  hipster append
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'a list) (zs :: 'a list) .
       ((append xs zs) = (append ys zs)) ==> (xs = ys)"
    oops
end
