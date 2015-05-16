theory prop_36
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (Nil2) = Nil2"
  | "takeWhile x (Cons2 z xs) =
       (if x z then Cons2 z (takeWhile x xs) else Nil2)"
  (*hipster takeWhile *)
  theorem x0 :
    "!! (xs :: 'a list) . (takeWhile (% (x :: 'a) => True) xs) = xs"
    by (hipster_induct_schemes)
end
