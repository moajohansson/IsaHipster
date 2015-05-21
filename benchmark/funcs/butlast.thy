theory butlast
imports Main
        "../data/list"
        "../funcs/append"
        "../../IsaHipster"

begin

fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
| "butlast (Cons2 y (Nil2)) = Nil2"
| "butlast (Cons2 y (Cons2 x2 x3)) = Cons2 y (butlast (Cons2 x2 x3))"

(*hipster butlast append*)

lemma unknown []: "butlast.butlast (append.append x x) = append.append x (butlast.butlast x)"
oops

end

