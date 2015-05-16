theory simp_expr_unambig5
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Tok = C | D | X | Y | Pl
  datatype T = TX | TY
  datatype E = Plus "T" "E" | Term "T"
  fun linTerm :: "T => Tok list" where
  "linTerm (TX) = Cons2 X (Nil2)"
  | "linTerm (TY) = Cons2 Y (Nil2)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun lin :: "E => Tok list" where
  "lin (Plus a b) =
     append (append (linTerm a) (Cons2 Pl (Nil2))) (lin b)"
  | "lin (Term t) = linTerm t"
  hipster linTerm append lin
  theorem x0 :
    "!! (u :: E) (v :: E) . ((lin u) = (lin v)) ==> (u = v)"
    oops
end
