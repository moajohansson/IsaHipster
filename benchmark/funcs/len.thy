theory lem
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
| "len (Cons2 y xs) = S (len xs)"

end

