theory simp_expr_unambig3
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Tok = C | D | X | Y | Pl
  datatype E = Plus "E" "E" | EX | EY
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun lin :: "E => Tok list" where
  "lin (Plus a b) =
     append
       (append (append (cons C (nil)) (lin a)) (cons D (cons Pl (nil))))
       (lin b)"
  | "lin (EX) = cons X (nil)"
  | "lin (EY) = cons Y (nil)"
  theorem x0 :
    "!! (u :: E) (v :: E) . ((lin u) = (lin v)) ==> (u = v)"
    oops
end
