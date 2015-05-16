theory simp_expr_unambig1
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Tok = C | D | X | Y | Pl
  datatype E = Plus "E" "E" | EX | EY
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun lin :: "E => Tok list" where
  "lin (Plus a b) =
     append
       (append
          (append (append (Cons2 C (Nil2)) (lin a)) (cons2 Pl (nil2)))
          (lin b))
       (Cons2 D (Nil2))"
  | "lin (EX) = Cons2 X (Nil2)"
  | "lin (EY) = Cons2 Y (Nil2)"
  hipster append lin
  theorem x0 :
    "!! (u :: E) (v :: E) . ((lin u) = (lin v)) ==> (u = v)"
    oops
end
