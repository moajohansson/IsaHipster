theory prop_04
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun double :: "Nat => Nat" where
  "double (Z) = Z"
  | "double (S y) = S (S (double y))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster length double append *)

hipster double

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes length.simps append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes length.simps append.simps)

(*hipster double length append*)
lemma unknown []: "length (append x y) = length (append y x)"
oops

lemma unknown []: "length (append x x) = double (length x)"
oops

(*
Trivial proof: append (Cons2 x Nil2) y = Cons2 x y 
Trivial proof: length (Cons2 x Nil2) = S Z 
Trivial proof: S (S Z) = double (S Z) 
Trivial proof: append (Cons2 x Nil2) (append y z) = Cons2 x (append y z) 
Trivial proof: append (Cons2 x Nil2) (Cons2 y z) = Cons2 x (Cons2 y z) 
Trivial proof: append (Cons2 x Nil2) (append y y) = Cons2 x (append y y) 
Trivial proof: append (Cons2 x Nil2) (Cons2 x y) = Cons2 x (Cons2 x y) 
Trivial proof: append (Cons2 x Nil2) (Cons2 y Nil2) = Cons2 x (Cons2 y Nil2) 
Trivial proof: append (Cons2 x Nil2) (Cons2 x Nil2) = Cons2 x (Cons2 x Nil2) 

Trivial proof: length (Cons2 x y) = length (Cons2 z y) 
*)
(*
lemma ax: "length (append (Cons2 ya xs) y) = S (length (append xs y))"
by (metis length.simps(2) append.simps(2))

lemma ax2[thy_expl]: "length (append y (Cons2 ya xs)) = S (length (append y xs))"
by(hipster_induct_schemes)*)

  theorem x0 :
    "(length (append x x)) = (double (length x))"
    by (hipster_induct_schemes append.simps double.simps length.simps list.exhaust Nat.exhaust)

    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
