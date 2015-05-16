theory prop_44
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = nil2"
  | "zip (Cons2 z x2) (Nil2) = nil2"
  | "zip (Cons2 z x2) (cons2 x3 x4) = cons2 (Pair z x3) (zip x2 x4)"
  fun zipConcat :: "'a => 'a list => 'b list =>
                    (('a, 'b) Pair2) list" where
  "zipConcat x y (Nil2) = nil2"
  | "zipConcat x y (Cons2 y2 ys) = cons2 (Pair x y2) (zip y ys)"
  hipster zip zipConcat
  theorem x0 :
    "!! (x :: 'a) (xs :: 'a list) (ys :: 'b list) .
       (zip (Cons2 x xs) ys) = (zipConcat x xs ys)"
    oops
end
