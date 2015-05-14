theory list_Select
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun select2 :: "'a => (('a, ('a list)) Pair2) list =>
                  (('a, ('a list)) Pair2) list" where
  "select2 x (nil) = nil"
  | "select2 x (cons (Pair y2 ys) x2) =
       cons (Pair y2 (cons x ys)) (select2 x x2)"
  fun select :: "'a list => (('a, ('a list)) Pair2) list" where
  "select (nil) = nil"
  | "select (cons y xs) = cons (Pair y xs) (select2 y (select xs))"
  fun map2 :: "('t2 => 't) => 't2 list => 't list" where
  "map2 f (nil) = nil"
  | "map2 f (cons y z) = cons (f y) (map2 f z)"
  fun fst :: "('a, 'b) Pair2 => 'a" where
  "fst (Pair y z) = y"
  theorem x0 :
    "!! (xs :: 't list) .
       (map2 (% (x :: ('t, ('t list)) Pair2) => fst x) (select xs)) = xs"
    oops
end
