theory prop_61
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  fun lastOfTwo :: "Nat list => Nat list => Nat" where
  "lastOfTwo x (Nil2) = last x"
  | "lastOfTwo x (Cons2 z x2) = last (Cons2 z x2)"
  fun append :: "Nat list => Nat list => Nat list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster last lastOfTwo append *)

(*hipster lastOfTwo*)(*
lemma lemma_a [thy_expl]: "last x2 = lastOfTwo x2 x2"
by (hipster_induct_schemes lastOfTwo.simps)
(*hipster append last*)

lemma lemma_aa [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes append.simps last.simps)

lemma lemma_ab [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes append.simps last.simps)

lemma unknown [thy_expl]: "last (append x x) = last x"
oops*)

(*hipster lastOfTwo last append*)

  theorem x0 :
    "(last (append xs ys)) = (lastOfTwo xs ys)"
    by (hipster_induct_schemes last.simps append.simps lastOfTwo.simps list.exhaust Nat.exhaust)

end
