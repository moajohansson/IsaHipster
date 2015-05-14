theory simp_expr_unambig5
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Tok = C | D | X | Y | Pl
  datatype T = TX | TY
  datatype E = Plus "T" "E" | Term "T"
  fun linTerm :: "T => Tok list" where
  "linTerm (TX) = cons X (nil)"
  | "linTerm (TY) = cons Y (nil)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun lin :: "E => Tok list" where
  "lin (Plus a b) =
     append (append (linTerm a) (cons Pl (nil))) (lin b)"
  | "lin (Term t) = linTerm t"
  theorem x0 :
    "!! (u :: E) (v :: E) . ((lin u) = (lin v)) ==> (u = v)"
    oops
end
