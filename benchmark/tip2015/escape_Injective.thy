theory escape_Injective
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
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
  "escape (Nil2) = nil2"
  | "escape (Cons2 y xs) =
       (if isSpecial y then Cons2 ESC (cons2 (code y) (escape xs)) else
          Cons2 y (escape xs))"
  hipster isSpecial code escape
  theorem x0 :
    "!! (xs :: Token list) (ys :: Token list) .
       ((escape xs) = (escape ys)) ==> (xs = ys)"
    oops
end
