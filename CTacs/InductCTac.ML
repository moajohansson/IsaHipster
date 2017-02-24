(*  Author:     Moa Johansson, Chalmers University of Technology *)

(* Contextual tactics: Tactics that carry a context to record what they do.
   useful for tactics that do search, e.g. induction, then we can record
   what induction scheme, induction variables and lemmas were needed for
   a successful proof.
*)

signature INDUCT_CTAC =
sig

type inductionStrategy


val sledgehammer_ctac : int -> CTac.ctactic
val simp_goal_ctac: int -> CTac.ctactic
val simp_or_sledgehammer_ctac : int -> CTac.ctactic

val induct_and_sledgehammer_ctac : inductionStrategy
val induct_and_simp_ctac : inductionStrategy

val structural_induction_ctac : inductionStrategy -> int -> CTac.ctactic
val recursion_induction_ctac : inductionStrategy -> int -> CTac.ctactic

val hipster_induct : Proof.context -> tactic
val thy_expl_hard_ctac : CTac.ctactic
end

structure Induct_CTac  : INDUCT_CTAC   =
struct

(* Arguments to inductionStrategy type:
  (string * Thm.thm list) option:
    Name of induction theorem plus the theorem(s) as Isabelle return a list when looking up a name.
    If NONE, this means we just try structural induction.
  string list :
    The variables we apply induction too. Must match those in induction scheme.
  ctactic :
    The actual ctactic, which applies induction and tries to solve step- and basecases.
  *)
type inductionStrategy =  (string * Thm.thm list) option -> string list -> CTac.ctactic


fun sledgehammer_ctac i (ctxt,thm) =
  case (Hipster_Sledgehammer_Tactics.sledgehammer_get_tac ctxt []
                                        Sledgehammer_Fact.no_fact_override [] i thm) of
  SOME (meth_tac, (meth, facts)) =>
    let
    val hipster_meth = Induction_Data.Sledgehammer_Meth meth
  in
    Seq.map
    (fn nwthm => (Induction_Data.add_subgoal_tac_ctxt 
                   (i, (hipster_meth,facts)) ctxt, nwthm))
       (meth_tac i thm) 
  end
 | NONE => Seq.single (ctxt, thm) (* Do nothing - Sledgehammer failed. *)
  

(* Apply simp to subgoal i and record that we've done that,
   if simp managed to somehow make progress. *)
fun simp_goal_ctac i (ctxt,thm) =
  Seq.map
    (fn (ctxt',thm') => (Induction_Data.add_subgoal_tac_ctxt 
                        (i, (Induction_Data.Sledgehammer_Meth Sledgehammer_Proof_Methods.Simp_Method, [])) 
                        ctxt',thm'))
     (CTac.AS_CTACTIC (CHANGED (Simplifier.asm_full_simp_tac ctxt i)) (ctxt,thm))

(* Must fail if there are any open subgoals left *)
val simp_or_sledgehammer_ctac =
  (*   CTac.SOLVE_OR_FAIL (CTac.ALLGOALS (CTac.CTHEN_MAYBE'( 
                                          simp_goal_ctac, sledgehammer_ctac))) *)
  CTac.CTHEN_MAYBE' (simp_goal_ctac, sledgehammer_ctac)                               


(* Apply induction and record which rule was used, and on which variables *)
fun induct_on_var_ctac rule var i (ctxt,thm) =
  let
    val (ithings, _) = Ind_Tacs.inductable_things_in_sg ctxt i thm;
    val (otherfrees, inductfrees) = Ind_Tacs.mk_induct_insts ithings var  
    val insts = map (fn NONE => NONE
                        | SOME v => SOME (NONE : Binding.binding option,(Free v,false)))
                  inductfrees
        
    val rule' = case rule of NONE => NONE | SOME (_,thms) => SOME thms
       
    val results = Induction.induction_tac ctxt false
                      [insts] [otherfrees] [] rule' [] i thm
                    handle ERROR msg => (warning ("Error in: " ^ msg ^ "\n"); Seq.empty)
                    handle Fail  msg => (warning ("Failure in: *" ^ msg ^"\n"); Seq.empty)
                    (*Ind_Tacs.induct_on_var_tac ctxt rule (SOME var) i thm*)

    (* If rule is NONE, we do structural induction *)
    fun set_rule r  = case r of NONE => Induction_Data.set_induction_rule_ctxt NONE
                              | SOME (nm,_) => Induction_Data.set_induction_rule_ctxt (SOME nm)
  in
    Seq.map (fn thm' =>
      (ctxt     (* FIXME: Need to also set non-induct vars as arbitrary in Isar *)
       |> Induction_Data.set_induction_vars_ctxt var
       |> Induction_Data.set_arbitrary_vars_ctxt (map fst otherfrees) 
       |> set_rule rule, thm')) results
  end;

(* Note: ALLGOALS will do subgoals in reverse order, starting with the highest number, working backwards! *)
(* Note 2: auto always applies to all subgoals, so need to merge if two auto's are after one another. *) 
fun induct_and_sledgehammer_ctac rule var = 
  CTac.SOLVE_OR_FAIL 
  (CTac.CTHEN(
    Seq.DETERM (CTac.HEADGOAL (induct_on_var_ctac rule var)),
    CTac.ALLGOALS  simp_or_sledgehammer_ctac))

fun induct_and_simp_ctac rule var =
  CTac.SOLVE_OR_FAIL
    (CTac.CTHEN(
         Seq.DETERM (CTac.HEADGOAL (induct_on_var_ctac rule var)), 
         CTac.ALLGOALS simp_goal_ctac))

(* Try induction (using the strategy strat)
   on each variable in vars, until we find one that allows a proof.
   rule states if we are to use some particular induction rule, e.g.
   recursion induction. If rule is NONE, we do stuctural induction. *)
fun try_induct_on_ctac rule strat vars i (ctxt,thm) =
  let
  val ctxt2 = Induction_Data.reset_ind_proof_data_ctxt ctxt
  in
  (case vars of
    []        => CTac.no_ctac
  | (v :: vs) =>
    CTac.CORELSE (* Commits to first if that return non-empty sequence *)
      (strat rule v,
      try_induct_on_ctac rule strat vs i)
   ) (ctxt2,thm)
  end;

(* Structural Induction: Find the variables we can induct on *)
fun structural_induction_ctac strat i (ctxt,thm) =
    let
      val vars = map (fn (v,_) => [v]) (fst (Ind_Tacs.inductable_things_in_sg ctxt i thm))
    in
      (try_induct_on_ctac NONE strat vars i) (ctxt,thm)
    end;

(* Recursion Induction: Search over possible function we can get an induction scheme from. *)
(* Q: Shouldn't this do just recursion induction, so we can have a separate tactic for trying
   both this and structural? *)

  fun reP uu = case uu of
        Var (_,t) => t
      | (t$_) => reP t
      | (Abs (_, t, _)) => t
      | (Free (_, t)) => t; (* TODO: Bound, Const *)

fun try_rec_induction_schemes_ctac scheme_rules strat vars i =
  case scheme_rules of
        [] => CTac.no_ctac (* try_induct_on_ctac NONE strat vars i *)
      | ((n,r)(*ind_scheme*) :: rs) =>
        let
          val argTyps = binder_types (reP (HOLogic.dest_Trueprop (Thm.concl_of (hd r))))
          val all_instances = (Scheme_Instances.instances_for_with argTyps vars)
          val instt = hd all_instances
        in
          CTac.CORELSE
          (try_induct_on_ctac (SOME (n,r)(*ind_scheme*)) strat (map (map fst) instt) (*vars*) i,
          (try_rec_induction_schemes_ctac rs strat vars i))
        end;

fun recursion_induction_ctac strat i (ctxt,thm) =
  let
      val vars = (*map (fn (v,_) => v*) (fst (Ind_Tacs.inductable_things_in_sg ctxt i thm))
      val thynm = Context.theory_name (Proof_Context.theory_of ctxt)
      val consts = Hipster_Utils.thy_consts_of thynm thm
      val schemes =  map_filter (try (fn n => (n, Sledgehammer_Util.thms_of_name ctxt n)))
                            (distinct (op =) (map (fn c => (c^".induct")) consts))
      (* Q: Do we need to reverse this? *)
      (* val schemes = (*rev*) thinds *)
    in
      try_rec_induction_schemes_ctac schemes strat vars i (ctxt,thm)
    end;

(* A tactic for automated induction to be called from Isar method hipster_induct, see IsaHipster.thy
  It does the search over which variables one could do structural induction, or else which functions
  one can do recursion induction over and then
  follows by simp or sledgehammer.
  Outputs a snippet of Isar for the proof found, which only used standard Isabelle tactics and avoid
  repeating search. *)
fun hipster_induct ctxt0 thm =
  let
    val ctxt = Induction_Data.reset_ind_proof_data_ctxt ctxt0
    val result = (* CTac.ALLGOALS (structural_induction_ctac induct_and_simp_ctac) (ctxt,thm) *)
                 (* CTac.ALLGOALS (recursion_induction_ctac induct_and_sledgehammer_ctac) (ctxt,thm) *)
                 (CTac.CORELSE
                  ( CTac.ALLGOALS (structural_induction_ctac induct_and_sledgehammer_ctac),
                    CTac.ALLGOALS (recursion_induction_ctac induct_and_sledgehammer_ctac)))                    
                 (ctxt,thm) 
    in
      case (Seq.list_of result) of 
      [] => Seq.empty
      | ((ctxt1,thm1)::_) => (* NOTE: Check if proved! otherwise fail *)
          (if (Thm.no_prems thm1) then  (* proved thm, no subgoals *)
                let val _ = Sledgehammer_Util.with_vanilla_print_mode writeln
                                   (Active.sendback_markup [Markup.padding_command]
                                     (Induction_Data.get_proof_script_ctxt ctxt1))
                   in Seq.single thm1 end
          else Seq.empty)
    end                              
(* Same as above, but no proof output directly. To be used only during theory exploration*)
fun thy_expl_hard_ctac (ctxt0, thm) =
   let
    val ctxt = Induction_Data.reset_ind_proof_data_ctxt ctxt0
    in (*CTac.ALLGOALS (recursion_induction_ctac induct_and_sledgehammer_ctac (*induct_and_simp_ctac *)) (ctxt,thm) *)
       CTac.ALLGOALS (structural_induction_ctac induct_and_sledgehammer_ctac) (ctxt,thm)
     (* (CTac.CORELSE
                  ( CTac.ALLGOALS (structural_induction_ctac induct_and_sledgehammer_ctac),
                    CTac.ALLGOALS (recursion_induction_ctac induct_and_sledgehammer_ctac)))
                 (ctxt,thm) *)
    end;
end
