theory Dev
imports "$HIPSTER_HOME/IsaHipster"

begin

setup Tactic_Data.set_induct_simp

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree""'a Tree"

ML{*

Sledgehammer.run_sledgehammer;
Toplevel.proof_of;

fun my_sledgehammer state minimiser = 
  let 
  (* val state = Toplevel.proof_of @{Isar.state} *)
  val thy =  Proof.theory_of state 
  in    
  Sledgehammer.run_sledgehammer 
    (Sledgehammer_Commands.default_params thy [])
    Sledgehammer_Prover.Try
    NONE
    1
    Sledgehammer_Fact.no_fact_override
    minimiser
    state
  end; 
*}
fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

fun tmap :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "tmap f (Leaf x) = Leaf (f x)"
| "tmap f (Node l r) = Node (tmap f l) (tmap f r)" 

(* First call to Hipster: Explore tmap and mirror *)
(* hipster tmap mirror *)
lemma lemma_a [thy_expl]: "mirror (tmap x2 y2) = tmap x2 (mirror y2)"
apply (induct y2)
apply @{tactic }
done


lemma lemma_aa [thy_expl]: "mirror (mirror x2) = x2"
by hipster_induct_simp

end
