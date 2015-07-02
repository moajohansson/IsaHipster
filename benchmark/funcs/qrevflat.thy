theory qrevflat
imports Main
        "../data/list"
        "../funcs/append"
        "../funcs/rev"
        "$HIPSTER_HOME/IsaHipster"

begin

fun qrevflat :: "('a list) list => 'a list => 'a list" where
  "qrevflat (Nil2) y = y"
| "qrevflat (Cons2 xs xss) y = qrevflat xss (append (rev xs) y)"

end

