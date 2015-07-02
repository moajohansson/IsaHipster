theory mirror
imports Main
        "../data/Tree"
        "$HIPSTER_HOME/IsaHipster"

begin

fun mirror :: "'a Tree => 'a Tree" where
  "mirror (Leaf) = Leaf"
| "mirror (Node l y r) = Node (mirror r) y (mirror l)"

(*hipster mirror*)

lemma lemma_ta [thy_expl]: "mirror (mirror x2) = x2"
by (hipster_induct_schemes mirror.simps)

end

