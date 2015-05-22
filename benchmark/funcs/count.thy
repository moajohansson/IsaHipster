theory count
imports Main
        "../data/Nat"
        "../data/list"
        "../funcs/equal"
        "../funcs/append"
        "../../IsaHipster"

begin

fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
| "count x (Cons2 z ys) =
     (if equal2 x z then S (count x ys) else count x ys)"

(* trivial
hipster count *)

(*trivial
hipster equal2 count*)

(*trivial
hipster_cond equal2 count append*)

end

