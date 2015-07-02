theory map
imports Main
        "../data/list"
        "$HIPSTER_HOME/IsaHipster"

begin

fun map2 :: "('a => 'b) => 'a list => 'b list" where
  "map2 x (Nil2) = Nil2"
| "map2 x (Cons2 z xs) = Cons2 (x z) (map2 x xs)"
thm map2.induct
end

