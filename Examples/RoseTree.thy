theory RoseTree
  imports Main "$HIPSTER_HOME/IsaHipster"
    "~~/src/HOL/Library/BNF_Corec"
begin
(* Set Hipster tactic *)
setup Tactic_Data.set_sledgehammer_coinduct 
setup Misc_Data.set_noisy
setup Misc_Data.set_time
setup Misc_Data.set_hammer_timeout_medium
setup Tactic_Data.set_no_proof
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

primcorec mirror :: "'a Tree \<Rightarrow> 'a Tree"
  where "mirror t = Node (lab t) (rev (sub t))"
(* thm Tree.coinduct_strong *)

primcorec tmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Tree \<Rightarrow> 'b Tree"
  where "tmap f t = Node (f (lab t)) (map (tmap f) (sub t))"

cohipster mirror (* 29.345s elapsed time, 7.060s cpu time, 1.694s GC time *)
lemma lemma_a [thy_expl]: "mirror (mirror y) = y"
  by (simp add: Tree.expand)

cohipster mirror tsum (*597.303s elapsed time, 83.481s cpu time, 9.110s GC time *)
lemma lemma_aa [thy_expl]: "tsum (mirror x) (mirror x) = mirror (tsum x x)"
  by (metis (no_types, lifting) mirror.code mirror.simps(1) mirror.simps(2) rev_map tsum.ctr tsum.simps(1) tsum.simps(2) zip_rev)
    
lemma unknown [thy_expl]: "tsum y x = tsum x y"
  oops
    
lemma unknown [thy_expl]: "tsum (tsum x y) z = tsum x (tsum y z)"
  oops
    
lemma unknown [thy_expl]: "mirror (tsum x (mirror x)) = tsum x (mirror x)"
  oops
    
lemma unknown [thy_expl]: "mirror (tsum x (mirror (tsum x x))) = tsum x (tsum x (mirror x))"
  oops
    
lemma unknown [thy_expl]: "mirror (tsum x (tsum x (mirror x))) = tsum x (mirror (tsum x x))"
  oops
    
lemma unknown [thy_expl]: "tsum (mirror x) (mirror (tsum x x)) = mirror (tsum x (tsum x x))"
  oops

cohipster mirror tmap (* 102.723s elapsed time, 23.739s cpu time, 2.948s GC time*)
lemma lemma_ab [thy_expl]: "tmap z (mirror x2) = mirror (tmap z x2)"
  by (simp add: mirror.code rev_map tmap.code)

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