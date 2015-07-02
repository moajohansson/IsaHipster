theory len
imports Main
        "../data/list"
        "../data/Natu"
        "$HIPSTER_HOME/IsaHipster"

begin

fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
| "len (Cons2 y xs) = S (len xs)"

end

