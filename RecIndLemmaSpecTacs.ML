(*  Author:     Moa Johansson, Chalmers University of Technology

Tactic for doing recursion induction, or else trying to generalise and prove a
lemma instead (also by recursion induction), as suggested by Koen Claessen.

*)

structure Rec_Ind_Lemma_Spec_Tacs   =
struct

fun zip_to_app 0 z = z
  | zip_to_app n z = zip_to_app (n-1) (Zipper.move_up z);

(* Introduce a new variable in lemma *)
fun varify (arg, (used_names, nw_args)) = 
  if (Term.is_Free arg orelse Term.is_Var arg) then
      (used_names, (NONE, arg)::nw_args) (* No need to generalise args that already are variables *)
  else
    let 
      val (new_name,used_names') = Name.variant "x" used_names
    in
      (used_names', (SOME arg, Free(new_name, Term.type_of arg))::nw_args)
    end

(* Introduce condition relating new variable to appropriate subterm in lemma *)
fun mk_conds (NONE,_) = NONE (* Case where arg already was a variable *)
  | mk_conds (SOME arg, nw_var as Free(_,typ)) = 
    SOME (@{term HOL.Trueprop} $ (Term.list_comb (Const("HOL.eq",[typ,typ]---> @{typ bool}), [nw_var,arg])))
  | mk_conds _ = raise error "mk_conds: New variable is not a Free!"; (* NONE; This shouldn't ever happen, means the new variable isn't a variable. *)

(* Construct a lemma which would enable recursion induction to be applied to the function we're at in zipper.*)
fun conj_lemma (z, _) =
   case z of 
   (Const(_,ty),_) =>  (* The zipper z is located at a function we could do recursion induction on. *)
      let 
        (* Zip to whole subterm whose head is the fun we want to do recursion indcution on *)
        val zip_appl = zip_to_app (length (fst (Term.strip_type ty))) z 
        (* Split into function f and list of its args *)
        val (f, args) = Term.strip_comb (Zipper.trm zip_appl)
        (* names used in this term *)
        val used_names = Name.make_context (map fst (Hipster_Utils.frees_of (Zipper.top_trm z)))
        (* Maybe replace some args by fresh variables *)
        val (_, args') = List.foldr varify (used_names,[]) args (* Important: same order of args as before *)
        (* Re-assemble potentially generalised term *)
        val new_trm = Term.list_comb (f, (map snd args'))
        val nw_zipper = Zipper.set_trm new_trm zip_appl
        val conds =  map_filter mk_conds args'

     in 
        if (conds = []) then NONE
        (* Attach new conditions to the term *)
        else SOME (List.foldr (fn (cond,trm) =>  Term.list_comb (@{term Pure.imp}, [cond, trm]))
                         (Zipper.trm  (Zipper.goto_top nw_zipper)) 
                         conds) 
    end
  | _ => NONE (* This shouldn't happen, we should only use this function on a zipper at suitable location.
                  Mabye raise exception here instead! *)

(* Figure out where recursion induction could potentially be applied. *)
fun inductable_pos_of_funs ctxt trm  =
  let
    val thm_zip = Zipper.mktop trm; 
    val all_leaves = Seq.list_of (ZipperSearch.leaves_lr thm_zip);

    (* positions of functions  with a rec. induction theorem. *)
    fun inductable_fun_in_zipper z =
      case z of 
      (Const(cnm,_),_) => 
          let val recind_nm = cnm^".induct"
          in  
          SOME (z, (recind_nm, (Sledgehammer_Util.thms_of_name ctxt recind_nm)))
          handle ERROR _ =>  NONE
          end
      | _ => NONE; 

    val all_inductable_funs = map_filter inductable_fun_in_zipper all_leaves;

    val inductable_pos = map_filter Rec_Ind_Tacs.is_rec_ind_applicable all_inductable_funs
  in
    inductable_pos  
  end;

(* FIXME: Use Pretty to make sure indentations are done properly instead of spaces... *)
(* Maybe move to LemmaData.ML*)
 fun mk_proof_str_w_lemma ctxt  = 
   let
    val lemma = the (Lemma_Data.lemma_of_ctxt ctxt);
    val vars_n_types = Hipster_Utils.frees_of (Thm.prop_of lemma)
    val lemma_str = Library.quote (Syntax.string_of_term ctxt (Thm.prop_of lemma))
    val vars_str = String.concatWith " " (map fst vars_n_types);
    val tactic_str = Lemma_Data.lemma_tac_of_ctxt ctxt 
    val other_tac_str = Lemma_Data.goal_tac_of_ctxt ctxt   
  in
    "proof- \n  have " ^ lemma_str ^ " for " ^ vars_str ^ 
    "\n    by " ^ tactic_str  ^"\n" ^ "  then show ?thesis by " ^ other_tac_str ^"\nqed"
  end

(* Tactic to check if a goal is solvable by the given lemma. *)
fun solve_goal_by_lemma_ctac lemma i (ctxt0,thm) =
  let
    (* Generalise lemma to get version with meta-variables instead. *)
    val gen_lemma = Drule.generalize (Hipster_Utils.frees_and_tfrees_of_thm lemma) lemma
    val ctxt = Simplifier.add_simp gen_lemma ctxt0
  in  
  Seq.map
    (fn (ctxt',thm') => ((Lemma_Data.set_lemma_ctxt (SOME lemma) ctxt')
                         |> Lemma_Data.set_goal_tac_ctxt ("simp[" ^ Library.string_of_int i ^ "]"), thm'))                                     
     (CTac.AS_CTACTIC (SOLVED' (Simplifier.asm_full_simp_tac ctxt) i) (ctxt,thm))
 end

(* Produce a lemma, prove it by recursion induction and solve original goal. *)
fun try_mk_lemma_ctac i (ctxt, thm)  = 
 let
    val trm = Hipster_Utils.strip_Prop (Thm.concl_of thm)
    
    val thm_zip = Zipper.mktop trm;
    val all_leaves = Seq.list_of (ZipperSearch.leaves_lr thm_zip);

    (* positions of functions  with a rec. induction theorem. *)
    fun inductable_fun_in_zipper z =
      case z of 
      (Const(cnm,_),_) => 
          let val recind_nm = cnm^".induct"
          in  
          SOME (z, (recind_nm, (Sledgehammer_Util.thms_of_name ctxt recind_nm)))
          handle ERROR _ =>  NONE
          end
      | _ => NONE; 

    val all_inductable_funs = map_filter inductable_fun_in_zipper all_leaves;
    val cand_lemmas = (map_filter conj_lemma all_inductable_funs)
    
    fun init_and_prove_by tac ctxt trm = 
      case (SINGLE (tac ctxt) (Goal.init (Thm.cterm_of ctxt trm))) of
            NONE => NONE
          | SOME thm => if (Thm.no_prems thm) then SOME (Goal.finish ctxt thm) else NONE (* Check proved i.e. no open subgoals *)
              
    val proved_lemmas =  map_filter (init_and_prove_by (Rec_Ind_Tacs.recinduct_simp) ctxt) cand_lemmas
    val ctxt1 =  Lemma_Data.set_lemma_tac_ctxt "hipster_recind_simp" ctxt
    (* val gen_lemmas = map (fn lemma => Drule.generalize (Hipster_Utils.frees_and_tfrees_of_thm lemma) lemma) proved_lemmas *)
    (* val try_lemma_tac = FIRST (map (fn l => Ind_Tacs.prove_by_simp ctxt [l]) gen_lemmas);*)
    val try_lemma_ctac = CTac.FIRST (map (fn l => solve_goal_by_lemma_ctac l i) proved_lemmas);
  in
  case inductable_pos_of_funs ctxt1 trm of
    [] => try_lemma_ctac (ctxt1,thm)
  | (_::_) => Seq.empty (* If you can do normal recursion induction, try that instead first. *)
 end;


(* With Isar output including rec-ind lemma and the whole shebang *) 
fun koen_induct ctxt0 thm =
  let
    val ctxt = ctxt0 |> Lemma_Data.reset_lemma_data_ctxt
                     |> Config.put show_types true
    val result = CTac.SINGLE (CTac.HEADGOAL try_mk_lemma_ctac) (ctxt,thm)            
    in
      case result of 
        NONE => Seq.empty
      | SOME (ctxt1, thm1) => 
          if (Thm.no_prems thm1) then  (* proved thm, no subgoals *)
            let val _ = writeln (Active.sendback_markup_command
                                       (mk_proof_str_w_lemma ctxt1))
             in Seq.single thm1 end
          else Seq.empty
    end

end