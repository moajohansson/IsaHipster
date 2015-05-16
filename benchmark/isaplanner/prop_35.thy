theory prop_35
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (Nil2) = Nil2"
  | "dropWhile x (Cons2 z xs) =
       (if x z then dropWhile x xs else Cons2 z xs)"
  (*hipster dropWhile *)
  theorem x0 :
    "!! (xs :: 'a list) . (dropWhile (% (x :: 'a) => False) xs) = xs"
    by (hipster_induct_schemes)
end
