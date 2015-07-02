theory butlastConcat
imports Main
        "../data/list"
        "../funcs/append"
        "../funcs/butlast"
        "$HIPSTER_HOME/IsaHipster"

begin

fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (Nil2) = butlast x"
| "butlastConcat x (Cons2 z x2) = append x (butlast (Cons2 z x2))"

hipster butlastConcat

end

