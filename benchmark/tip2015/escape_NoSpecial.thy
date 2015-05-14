theory escape_NoSpecial
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Token = A | B | C | D | ESC | P | Q | R
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun isSpecial :: "Token => bool" where
  "isSpecial x =
     case x of
       | other => False
       | ESC => True
       | P => True
       | Q => True
       | R => True
     end"
  fun isEsc :: "Token => bool" where
  "isEsc x =
     case x of
       | other => False
       | ESC => True
     end"
  fun ok :: "Token => bool" where
  "ok x = or2 (~ (isSpecial x)) (isEsc x)"
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
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun all :: "('a => bool) => 'a list => bool" where
  "all x (nil) = True"
  | "all x (cons z xs) = and2 (x z) (all x xs)"
  theorem x0 :
    "!! (xs :: Token list) . all (% (x :: Token) => ok x) (escape xs)"
    oops
end
