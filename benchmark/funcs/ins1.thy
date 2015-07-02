theory ins1
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/equal"
        "$HIPSTER_HOME/IsaHipster"

begin

fun ins1 :: "Nat => Nat list => Nat list" where
  "ins1 x (Nil2) = Cons2 x (Nil2)"
| "ins1 x (Cons2 z xs) =
     (if equal2 x z then Cons2 z xs else Cons2 z (ins1 x xs))"

end

