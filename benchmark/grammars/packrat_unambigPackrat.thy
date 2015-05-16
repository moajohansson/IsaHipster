theory packrat_unambigPackrat
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Tok = X | Y | Z
  datatype B2 = SB "B2" | ZB
  datatype A2 = SA "A2" | ZA
  datatype S = A "A2" | B "B2"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun linA :: "A2 => Tok list" where
  "linA (SA a) =
     append (append (Cons2 X (Nil2)) (linA a)) (cons2 Y (nil2))"
  | "linA (ZA) = Cons2 X (cons2 Z (cons2 Y (Nil2)))"
  fun linB :: "B2 => Tok list" where
  "linB (SB b) =
     append
       (append (Cons2 X (Nil2)) (linB b)) (cons2 Y (cons2 Y (nil2)))"
  | "linB (ZB) = Cons2 X (cons2 Z (cons2 Y (cons2 Y (Nil2))))"
  fun linS :: "S => Tok list" where
  "linS (A a) = linA a"
  | "linS (B b) = linB b"
  hipster append linA linB linS
  theorem x0 :
    "!! (u :: S) (v :: S) . ((linS u) = (linS v)) ==> (u = v)"
    oops
end
