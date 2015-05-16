theory list_return_2
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun return :: "'a => 'a list" where
  "return x = Cons2 x (Nil2)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun bind :: "'a list => ('a => 'b list) => 'b list" where
  "bind (Nil2) y = nil2"
  | "bind (Cons2 z xs) y = append (y z) (bind xs y)"
  hipster return append bind
  theorem x0 :
    "!! (xs :: 'a list) . (bind xs (% (x :: 'a) => return x)) = xs"
    oops
end
