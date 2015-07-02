theory simp_expr_unambig4
imports Main
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Tok = C | D | X | Y | Pl

datatype E = Plus "E" "E" | Ex | EY

fun append :: "'a list => 'a list => 'a list" where
"append (nil2) y = y"
| "append (cons2 z xs) y = cons2 z (append xs y)"

fun linTerm :: "E => Tok list"
and     lin :: "E => Tok list" where
"linTerm (Plus y z) =
   append (append (cons2 C (nil2)) (lin (Plus y z))) (cons2 D (nil2))"
| "linTerm (Ex) = cons2 X (nil2)"
| "linTerm (EY) = cons2 Y (nil2)"
| "lin (Plus a b) =
     append (append (linTerm a) (cons2 Pl (nil2))) (linTerm b)"
| "lin (Ex) = cons2 X (nil2)"
| "lin (EY) = cons2 Y (nil2)"

thm linTerm_lin.induct
theorem x0 :
  "!! (u :: E) (v :: E) . (((lin u) = (lin v)) ==> (u = v))"
  oops

end
