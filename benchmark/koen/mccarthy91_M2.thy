theory mccarthy91_M2
imports Main
begin
  fun m :: "int => int" where
  "m x = (if x > 100 then x - 10 else m (m (x + 11)))"
  theorem x0 :
    "!! (n :: int) . (n >= 101) ==> ((m n) = (n - 10))"
    oops
end
