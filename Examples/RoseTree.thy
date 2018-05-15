theory RoseTree
  imports Main "$HIPSTER_HOME/IsaHipster"
    "~~/src/HOL/Library/BNF_Corec"
begin
(* Set Hipster tactic *)
setup Tactic_Data.set_sledgehammer_coinduct 
setup Misc_Data.set_noisy
setup Misc_Data.set_nitpick

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

(* Finitely branching Rose tree of pot infinite depth from Isabelle tutorial on corecursion. *)
codatatype 'a Tree = 
  Node (lab: 'a) (sub: "'a Tree list")


(* Note: In the co-induction tutorial, this function is defined using a type-class for plus.
This seem to cause a weird XML-error in PIDE/xml.ML so something goes wrong in translation.
Presumably due to TIP not really supporting type-classes. *)
primcorec tsum :: "nat Tree \<Rightarrow> nat Tree \<Rightarrow> nat Tree"
where "tsum t u = Node (lab t + lab u) (map (\<lambda>(t', u'). tsum t' u') (zip (sub t) (sub u)))" 
(*Bug? Error when generating observer functions. *)

primcorec flip :: "'a Tree \<Rightarrow> 'a Tree"
  where "flip t = Node (lab t) (rev (sub t))"
(* thm Tree.coinduct_strong *)

cohipster flip
lemma lemma_a [thy_expl]: "flip (flip y) = y"
  by (simp add: Tree.expand) 
cohipster flip tsum
lemma lemma_aa [thy_expl]: "tsum (flip x) (flip x) = flip (tsum x x)"
  by(coinduction arbitrary: x rule: Tree.coinduct_strong)
    (smt flip.simps(1) flip.simps(2) list.rel_refl list_all2_map2 list_all2_rev1 tsum.simps(1) tsum.simps(2) zip_rev)

lemma unknown [thy_expl]: "tsum y x = tsum x y"
  oops
    
lemma unknown [thy_expl]: "tsum (tsum x y) z = tsum x (tsum y z)"
  oops

lemma unknown [thy_expl]: "flip (tsum x (flip x)) = tsum x (flip x)"
  oops
    
lemma unknown [thy_expl]: "flip (tsum x (flip (tsum x x))) = tsum x (tsum x (flip x))"
  oops

lemma unknown [thy_expl]: "flip (tsum x (tsum x (flip x))) = tsum x (flip (tsum x x))"
  oops
    
lemma unknown [thy_expl]: "tsum (flip x) (flip (tsum x x)) = flip (tsum x (tsum x x))"
  oops


(* This is obviously false, but if we call normal hipster it is suggested. Cause error in 
coinduction tactic, but counter-example easily found by nitpick *)
ML{*
val t = @{term "Trueprop(sub z @ sub y = sub y @ sub z)"};
val t = @{term "Product_Type.Pair 1 2"};

val def_params = Nitpick_Commands.default_params @{theory} [];

fun goal_prop str ctxt =
  let val prop = Syntax.read_prop ctxt str
  in Proof.theorem NONE (K I) [[(prop, [])]] ctxt
  end;
val state = goal_prop "sub z @ sub y = sub y @ sub z" @{context} ;
val (res, l) = Nitpick.pick_nits_in_subgoal state def_params Nitpick.Normal 1 1;

fun nitpick_conj ctxt conj_str = 
  let
    val state = goal_prop conj_str ctxt
    val thy = Proof.theory_of state
    val def_params = Nitpick_Commands.default_params thy [];
    val (res, _) = Nitpick.pick_nits_in_subgoal state def_params Nitpick.Normal 1 1;
  in
    (res = Nitpick.genuineN)
  end 
(*val i = 0;
val n = 0;
val step = 0;
val state = Proof.init @{context};
val (answer, mystery_list) = Nitpick.pick_nits_in_term state def_params Nitpick.Normal 0 0 0 [] [] [] t;

 val genuine = (Nitpick.genuineN = answer); *)
 *}

end