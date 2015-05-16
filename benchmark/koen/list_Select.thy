theory list_Select
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun select2 :: "'a => (('a, ('a list)) Pair2) list =>
                  (('a, ('a list)) Pair2) list" where
  "select2 x (Nil2) = Nil2"
  | "select2 x (Cons2 (Pair y2 ys) x2) =
       Cons2 (Pair y2 (Cons2 x ys)) (select2 x x2)"
  fun select :: "'a list => (('a, ('a list)) Pair2) list" where
  "select (Nil2) = Nil2"
  | "select (Cons2 y xs) = Cons2 (Pair y xs) (select2 y (select xs))"
  fun map2 :: "('t2 => 't) => 't2 list => 't list" where
  "map2 f (Nil2) = Nil2"
  | "map2 f (Cons2 y z) = Cons2 (f y) (map2 f z)"
  fun fst :: "('a, 'b) Pair2 => 'a" where
  "fst (Pair y z) = y"
  hipster select2 select map2 fst
  theorem x0 :
    "!! (xs :: 't list) .
       (map2 (% (x :: ('t, ('t list)) Pair2) => fst x) (select xs)) = xs"
    oops
end
