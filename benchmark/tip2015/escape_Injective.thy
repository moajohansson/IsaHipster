theory escape_Injective
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Token = A | B | C | D | ESC | P | Q | R
  fun isSpecial :: "Token => bool" where
  "isSpecial x =
     case x of
       | other => False
       | ESC => True
       | P => True
       | Q => True
       | R => True
     end"
  fun code :: "Token => Token" where
  "code x =
     case x of
       | other => x
       | ESC => x
       | P => A
       | Q => B
       | R => C
     end"
  fun escape :: "Token list => Token list" where
  "escape (nil) = nil"
  | "escape (cons y xs) =
       (if isSpecial y then cons ESC (cons (code y) (escape xs)) else
          cons y (escape xs))"
  theorem x0 :
    "!! (xs :: Token list) (ys :: Token list) .
       ((escape xs) = (escape ys)) ==> (xs = ys)"
    oops
end
