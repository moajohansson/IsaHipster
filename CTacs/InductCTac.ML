
signature INDUCT_CTAC =
sig

type hardCTac = Thm.thm list option -> string list -> int -> CTac.ctactic 

val try_inductable_vars_ctac : hardCTac -> int -> CTac.ctactic
val sledgehammer_ctac : int -> CTac.ctactic

val test_tac : Proof.context -> tactic 
end

structure Induct_CTac (* : INDUCT_CTAC  *)= 
struct

type hardCTac =  Thm.thm list option -> string list -> int -> CTac.ctactic

(* Apply Sledgehammer and record which facts we need to give Metis to reconstruct proof *)
fun sledgehammer_ctac i(ctxt,thm) = 
  let
    val proved = ThyExpl_Data.proved_of_ctxt ctxt
    val (facts,metis_tac) = Hipster_Sledgehammer_Tactics.sledgehammer_with_metis_tac ctxt [] 
                              Sledgehammer_Fact.no_fact_override proved i thm
    val facts_str = String.concatWith " " (Library.distinct (op =) facts)
  in
    Seq.map 
    (fn nwthm => (Induction_Data.add_subgoal_tac_ctxt ("(metis " ^ facts_str ^ ")") ctxt, nwthm)) 
        (metis_tac thm)  
  end;

(* Apply simp to subgoal i and record that we've done that *)
fun simp_goal_ctac i (ctxt,thm) = 
  Seq.map 
    (fn (ctxt',thm') => (Induction_Data.add_subgoal_tac_ctxt "simp" ctxt',thm'))
    (CTac.AS_CTACTIC (Simplifier.asm_full_simp_tac ctxt i) (ctxt,thm))

(* TODO: Implement and record if simp or metis+which facts should be used to replay *)
val simp_or_sledgehammer_ctac = 
 (* (CTac.CTHEN ((CTac.TRY simp_goal_ctac), sledgehammer_ctac)) *)
   CTac.CORELSE (CTac.ALLGOALS simp_goal_ctac, CTac.ALLGOALS sledgehammer_ctac)


(* Apply induction and record which rule was used, and on which variables *)
fun induct_on_var_ctac rule var i (ctxt,thm) = 
  let 
    val results = Ind_Tacs.induct_on_var_tac ctxt rule (SOME var) i thm
    (* If rule is NONE, we do structural induction *)                
    fun set_rule r  = case r of NONE => Induction_Data.set_induction_rule_ctxt NONE
                              | SOME (nm,_) => Induction_Data.set_induction_rule_ctxt (SOME nm)
  in 
    Seq.map (fn thm' => 
      (ctxt 
       |> Induction_Data.set_induction_vars_ctxt var 
       |> set_rule rule, thm')) results
  end;



fun induct_and_sledgehammer_ctac rule var =
  CTac.DEPTH_SOLVE(
  CTac.CTHEN(  
    Seq.DETERM (CTac.HEADGOAL (induct_on_var_ctac rule var)),
    simp_or_sledgehammer_ctac))

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
    CTac.CORELSE
      (strat rule v,
      try_induct_on_ctac rule strat vs i)
   ) (ctxt2,thm)
  end;

(* Structural Induction: Find the variables we can induct on *)
fun try_inductable_vars_ctac strat i (ctxt,thm) = 
    let 
      val vars = map (fn (v,_) => [v]) (fst (Ind_Tacs.inductable_things_in_sg ctxt i thm))
    in 
      (try_induct_on_ctac NONE strat vars i) (ctxt,thm)
    end;

fun test_tac ctxt thm = 
  let 
  (* val _ = @{print} (Thm.nprems_of thm) *)
   val res = if (Thm.no_prems thm) then Seq.empty
             else (CTac.ALLGOALS (try_inductable_vars_ctac induct_and_sledgehammer_ctac) (ctxt,thm))
   
    val _ =  case (Seq.list_of res) of [] => ()
                  | ((ctxt1,_)::_) => (*@{print} (Induction_Data.get_proof_scrip_ctxt ctxt1) *)
                    Sledgehammer_Util.with_vanilla_print_mode writeln
                    (Active.sendback_markup [Markup.padding_command] (Induction_Data.get_proof_scrip_ctxt ctxt1))
   (* val _ =  @{print} thm1 *)
  in  
   (*Seq.map snd res *)
   all_tac thm
  end 
end