theory prop_28
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (nil) = nil"
  | "rev (cons y xs) = append (rev xs) (cons y (nil))"
  fun qrevflat :: "('a list) list => 'a list => 'a list" where
  "qrevflat (nil) y = y"
  | "qrevflat (cons xs xss) y = qrevflat xss (append (rev xs) y)"
  fun revflat :: "('a list) list => 'a list" where
  "revflat (nil) = nil"
  | "revflat (cons xs xss) = append (revflat xss) xs"
  theorem x0 :
    "!! (x :: ('a list) list) . (revflat x) = (qrevflat x (nil))"
    oops
end
