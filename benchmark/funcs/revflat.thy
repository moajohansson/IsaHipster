theory revflat
imports Main
        "../data/list"
        "../funcs/append"
        "../../IsaHipster"

begin

fun revflat :: "('a list) list => 'a list" where
  "revflat (Nil2) = Nil2"
| "revflat (Cons2 xs xss) = append (revflat xss) xs"

end

