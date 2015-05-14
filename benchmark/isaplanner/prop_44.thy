theory prop_44
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (nil) y = nil"
  | "zip (cons z x2) (nil) = nil"
  | "zip (cons z x2) (cons x3 x4) = cons (Pair z x3) (zip x2 x4)"
  fun zipConcat :: "'a => 'a list => 'b list =>
                    (('a, 'b) Pair2) list" where
  "zipConcat x y (nil) = nil"
  | "zipConcat x y (cons y2 ys) = cons (Pair x y2) (zip y ys)"
  hipster zip zipConcat
  theorem x0 :
    "!! (x :: 'a) (xs :: 'a list) (ys :: 'b list) .
       (zip (cons x xs) ys) = (zipConcat x xs ys)"
    oops
end
