theory packrat_unambigPackrat
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Tok = X | Y | Z
  datatype B2 = SB "B2" | ZB
  datatype A2 = SA "A2" | ZA
  datatype S = A "A2" | B "B2"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun linA :: "A2 => Tok list" where
  "linA (SA a) =
     append (append (cons X (nil)) (linA a)) (cons Y (nil))"
  | "linA (ZA) = cons X (cons Z (cons Y (nil)))"
  fun linB :: "B2 => Tok list" where
  "linB (SB b) =
     append (append (cons X (nil)) (linB b)) (cons Y (cons Y (nil)))"
  | "linB (ZB) = cons X (cons Z (cons Y (cons Y (nil))))"
  fun linS :: "S => Tok list" where
  "linS (A a) = linA a"
  | "linS (B b) = linB b"
  theorem x0 :
    "!! (u :: S) (v :: S) . ((linS u) = (linS v)) ==> (u = v)"
    oops
end
