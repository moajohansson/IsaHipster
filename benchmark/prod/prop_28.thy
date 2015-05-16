theory prop_28
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  fun qrevflat :: "('a list) list => 'a list => 'a list" where
  "qrevflat (Nil2) y = y"
  | "qrevflat (Cons2 xs xss) y = qrevflat xss (append (rev xs) y)"
  fun revflat :: "('a list) list => 'a list" where
  "revflat (Nil2) = Nil2"
  | "revflat (Cons2 xs xss) = append (revflat xss) xs"
  hipster append rev qrevflat revflat
  theorem x0 :
    "!! (x :: ('a list) list) . (revflat x) = (qrevflat x (Nil2))"
    oops
end
