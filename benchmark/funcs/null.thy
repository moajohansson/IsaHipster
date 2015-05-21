theory null
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun null :: "'a list => bool" where
  "null (Nil2) = True"
| "null (Cons2 y z) = False"

end
