theory Tree
imports "$HIPSTER_HOME/IsaHipster"

begin

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree" 'a "'a Tree"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun tmap :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "tmap f (Leaf x) = Leaf (f x)"
| "tmap f (Node l x r) = Node (tmap f l) (f x) (tmap f r)" 


(* Call to Hipster: Explore tmap and mirror *)
hipster tmap mirror

end
