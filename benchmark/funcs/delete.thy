theory delete
imports Main
        "../data/list"
        "../data/Natu"
        "../funcs/equal"
        "../funcs/append"
        "../../IsaHipster"

begin

fun delete :: "Nat => Nat list => Nat list" where
  "delete x (Nil2) = Nil2"
| "delete x (Cons2 z xs) =
     (if equal2 x z then delete x xs else Cons2 z (delete x xs))"

(*hipster delete*)
lemma lemma_ad [thy_expl]: "delete x9 (delete y9 z9) = delete y9 (delete x9 z9)"
by (hipster_induct_schemes delete.delete.simps)

lemma lemma_ae [thy_expl]: "delete x5 (delete x5 y5) = delete x5 y5"
by (hipster_induct_schemes delete.delete.simps)

(* trivial
hipster delete equal2 append*)

(* trivial
hipster_cond equal2 delete append*)

end
