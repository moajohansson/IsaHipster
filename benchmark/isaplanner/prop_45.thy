theory prop_45
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = nil2"
  | "zip (Cons2 z x2) (Nil2) = nil2"
  | "zip (Cons2 z x2) (cons2 x3 x4) = cons2 (Pair z x3) (zip x2 x4)"
  hipster zip
  theorem x0 :
    "!! (x :: 'a) (y :: 'b) (xs :: 'a list) (ys :: 'b list) .
       (zip (Cons2 x xs) (cons2 y ys)) = (cons2 (Pair x y) (zip xs ys))"
    oops
end
