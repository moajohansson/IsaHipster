theory len
imports Main
        "../data/list"
        "../data/Natu"
        "../../IsaHipster"

begin

fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
| "len (Cons2 y xs) = S (len xs)"

end

