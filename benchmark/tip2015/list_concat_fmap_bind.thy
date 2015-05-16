theory list_concat_fmap_bind
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun fmap :: "('a => 'b) => 'a list => 'b list" where
  "fmap x (Nil2) = Nil2"
  | "fmap x (Cons2 z xs) = Cons2 (x z) (fmap x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun bind :: "'a list => ('a => 'b list) => 'b list" where
  "bind (Nil2) y = Nil2"
  | "bind (Cons2 z xs) y = append (y z) (bind xs y)"
  fun concat2 :: "('a list) list => 'a list" where
  "concat2 (Nil2) = Nil2"
  | "concat2 (Cons2 xs xss) = append xs (concat2 xss)"
  hipster fmap append bind concat2
  theorem x0 :
    "!! (f :: ('a => 'b list)) (xs :: 'a list) .
       (concat2 (fmap f xs)) = (bind xs f)"
    oops
end
