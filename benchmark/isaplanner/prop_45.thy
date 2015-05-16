theory prop_45
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
  | "zip (Cons2 z x2) (Nil2) = Nil2"
  | "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip x2 x4)"
  (*hipster zip *)
  theorem x0 :
    "!! (x :: 'a) (y :: 'b) (xs :: 'a list) (ys :: 'b list) .
       (zip (Cons2 x xs) (Cons2 y ys)) = (Cons2 (Pair x y) (zip xs ys))"
    by (hipster_induct_schemes)
end
