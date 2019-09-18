theory prop_49
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
  | "butlast (Cons2 y (Nil2)) = Nil2"
  | "butlast (Cons2 y (Cons2 x2 x3)) =
       Cons2 y (butlast (Cons2 x2 x3))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (Nil2) = butlast x"
  | "butlastConcat x (Cons2 z x2) = append x (butlast (Cons2 z x2))"
  (*hipster butlast append butlastConcat *)
(*hipster butlast append*)(*
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes butlast.simps append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes butlast.simps append.simps)

lemma unknown [thy_expl]: "butlast (append x x) = append x (butlast x)"
oops

lemma lemma_ab [thy_expl]: "butlastConcat Nil2 x = butlast x"
by (hipster_induct_schemes butlast.simps append.simps)

lemma lemma_ac [thy_expl]: "append x (butlast x) = butlastConcat x x"
by (hipster_induct_schemes butlast.simps append.simps)*)
(*
hipster butlast butlastConcat append
*)
(*hipster butlastConcat butlast append*)

setup\<open>Hip_Tac_Ops.set_metis_to @{context} 3000\<close>
setup\<open>Hip_Tac_Ops.set_metis_filter @{context} (K false)\<close>

  theorem x0 :
    "(butlast (append xs ys)) = (butlastConcat xs ys)"
    by (hipster_induct_schemes butlastConcat.simps butlast.simps append.simps list.exhaust)

 
end
