theory double
imports Main
        "../data/Natu"
        "$HIPSTER_HOME/IsaHipster"
begin

fun double :: "Nat => Nat" where
  "double (Z) = Z"
| "double (S y) = S (S (double y))"

(* trivial
hipster double *)

end

