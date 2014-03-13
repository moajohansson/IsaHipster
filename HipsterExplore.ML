(* Call the HipSpec theory exploration system. Prove the resulting conjectures. Those provable by 
   routine reasoning are deemed non-interesting and discarded. Those requiring "hard" reasoning are
   kept. *)

functor Hipster_Explore_Fun (Expl_Tacs : THY_EXPL_TACS) = 
struct


(*-----------------------------------------------------------------------------------------*)
(* The proof-loop, trying to prove the conjectures found by HipSpec  *) 
(*-----------------------------------------------------------------------------------------*)
fun try_nxt_conj ctxt =
    case (ThyExpl_Data.open_conjs_of_ctxt ctxt) of
      (*retry open_conjs if we have some new proved since last time.*)
      [] => if (ThyExpl_Data.progress_of_ctxt ctxt) 
            then SOME (ctxt 
                         |> ThyExpl_Data.set_open_conjs_ctxt (ThyExpl_Data.failed_of_ctxt ctxt)
                         |> ThyExpl_Data.set_failed_ctxt []
                         |> ThyExpl_Data.set_progress_ctxt false)                
            else NONE

    | (c::cs) => (* try proving next open conj *) 
      let 
        val r = SINGLE (Expl_Tacs.routine_tac ctxt) c
        val lemma_str = (Syntax.string_of_term ctxt (Thm.concl_of c))
          val _ = (Sledgehammer_Util.with_vanilla_print_mode Output.urgent_message) 
                ("Proving: " ^ lemma_str)
      in
      case r of (* Discard this, it is trivial *)
        SOME _ => SOME (ThyExpl_Data.set_open_conjs_ctxt cs ctxt)
      | NONE =>
        let
          val res = SINGLE (Expl_Tacs.hard_tac ctxt) c 
        in
          (* Only care about first proof found *)
          (case res of 
             SOME proved_thm => 
             let                
               val (new_nm, ctxt') = ThyExpl_Data.fresh_name ctxt 
               (* Thm used by simp need to be lifted so it use meta-variables *)
               val final_thm = proved_thm 
                                 |> (Drule.generalize (Hipster_Utils.frees_and_tfrees_of_thm proved_thm))
                                 |> Goal.finish ctxt' 
                                 |> Thm.put_name_hint new_nm
             in
               SOME (ctxt'
                       |> ThyExpl_Data.set_open_conjs_ctxt cs
                       |> ThyExpl_Data.add_proved_ctxt final_thm
                       |> ThyExpl_Data.set_progress_ctxt true)
             end
           (* NONE indicates that the tactic failed to prove c *)
           | NONE => SOME (ctxt
                             |> ThyExpl_Data.set_open_conjs_ctxt cs
                             |> ThyExpl_Data.add_failed_ctxt c)
          )
        end
      end;

fun try_prove_priority_goal ctxt goal =
    let
      (* val res = SINGLE (Expl_Tacs.hard_tac ctxt) goal *)
      val res = SINGLE (Expl_Tacs.routine_tac ctxt) goal
    in 
      case res of
        SOME _ => SOME (ThyExpl_Data.set_priority_goal_ctxt NONE ctxt)
      | NONE => NONE
    end;

fun proof_loop_w_prio ctxt facts prio_goal_opt cand_lemmas_str =
    let 
      val ctxt' = ThyExpl_Data.init_expl ctxt facts prio_goal_opt
                                          (Library.split_lines (Library.trim_line cand_lemmas_str))     
      fun recf ctxt = 
          case (try_nxt_conj ctxt) of
            NONE => NONE (*ctxt *) (* No more lemmas to prove, not proved prio goal, fail. *)
          | SOME ctxt' => 
            (case (ThyExpl_Data.priority_goal_of_ctxt ctxt')
              of NONE => NONE (* There is no prio goals, so nothing to do! *)
            | SOME goal => 
              (case (try_prove_priority_goal ctxt' goal) of
                 NONE => recf ctxt'
               | SOME ctxt'' => SOME ctxt'') (* Proved the priority goal, we're done! *)
            )
    in
      recf ctxt'
    end

fun proof_loop ctxt facts cand_lemmas_str = 
     let 
      val ctxt' = ThyExpl_Data.init_expl ctxt facts NONE
                                          (Library.split_lines (Library.trim_line cand_lemmas_str))     
      fun recf ctxt = 
          case (try_nxt_conj ctxt) of
            NONE => ctxt
          | SOME ctxt' => recf ctxt'
     in
      recf ctxt'
     end

(*-----------------------------------------------------------------------------------------*)
(* Call HipSpec to generate a list of conjectures and produce suitable output to paste into
   proof script for discovered lemmas  *) 
(*-----------------------------------------------------------------------------------------*)

(* TO DO: Implement properly *)
val haskell_consts = [("List.rev","reverse"),("List.append","++")]

fun map_to_haskell isa_nm = 
    case (Library.find_first (fn (nm,_) => nm=isa_nm) haskell_consts)
         of NONE => isa_nm
          | SOME (_,hask_nm) => hask_nm;

(* 'const_nms' are the name of the constants we wish to include in the Haskell 
   file. They must be prefixed by the theory name. *)   
fun hipspec_explore ctxt const_nms =
    let
      val thy = Proof_Context.theory_of ctxt
      val thynm = Context.theory_name thy
      val outfile = Hipster_Setup.filepath^ (Context.theory_name thy) ^"_hipspec.hs"
      val const_nms' = map map_to_haskell const_nms
      (* Do we always want to have the --extra-trans flag? this means extra funs gets picked up, if they
         are in the def of any of the given const-nms *)                                                         
      val add_funs = List.foldl (fn (nm,s) => "--extra-trans "^(Long_Name.base_name nm)^ " "^s) " " const_nms';
      val hipspec_cmd = "hipspec "^ "--isabelle-mode " ^ add_funs  ^ outfile;

      val path_opt = SOME (Path.explode Hipster_Setup.filepath);    
      val _ = Code_Target.export_code thy const_nms [((("Haskell",thynm), path_opt), [])];
      val _ = Isabelle_System.bash (Hipster_Setup.hipspecifyer_cmd ^" H "^ 
                                    Hipster_Setup.filepath^thynm^".hs " ^outfile);
    in 
      fst (Isabelle_System.bash_output hipspec_cmd)
    end;


(* The output sting for each lemma discovered. *)
fun mk_lemma_str ctxt (lemma,tac_str) = 
    let    
      (* Print variables without ? *)
      val ctxt' = Config.put show_question_marks false ctxt
      (* Disables silly Isabelle YXML markup for printing *)
      val str_of_term = Sledgehammer_Util.with_vanilla_print_mode (Syntax.string_of_term ctxt')
      val lemma_str = Library.quote (str_of_term (Thm.concl_of lemma))
      val name = Long_Name.base_name(Thm.get_name_hint lemma)
    in
      ("lemma " ^ name ^" [thy_expl]: "^ lemma_str ^ "\n" ^tac_str)
    end;

fun prep_conjs ctxt conjs =
    let
      val thy = Proof_Context.theory_of ctxt
      val thynm = Context.theory_name thy
    in
      if (Config.get ctxt thy_interesting = false)
      then conjs (* Want eqs about all functions, also those not about funs def in this thy *)
      else filter (fn c => (not((Hipster_Utils.thy_consts_of thynm c) = []))) conjs
    end;
                                                                 
(* Outputs snippets of proof script with the discovered lemmas that can be pasted into the theory file. *)
fun explore ctxt const_nms =
    let
      val facts_nms = map (fn c => c^".simps") const_nms
      val facts = maps (fn n => Sledgehammer_Util.thms_of_name ctxt n
                       handle _ => []) facts_nms
      val tac_str = Expl_Tacs.final_tactic_str ctxt facts_nms
                        
      val conjs = hipspec_explore ctxt const_nms;

      val res_ctxt = proof_loop ctxt facts conjs
      val output = Library.space_implode "\n\n"
                     ((map (mk_lemma_str res_ctxt) 
                           (map (fn thm => (thm, tac_str)) (ThyExpl_Data.proved_of_ctxt res_ctxt)) 
                      @ (map (mk_lemma_str res_ctxt) 
                             (map (fn conj => (conj,"oops")) (ThyExpl_Data.failed_of_ctxt res_ctxt)))))
    in
      (res_ctxt, (Sledgehammer_Util.with_vanilla_print_mode Output.urgent_message) 
         (Active.sendback_markup [Markup.padding_command] output))
    end;

(* A function which can be wrapped in Isabelle's setup command from a theory file.
   It adds the discovered lemmas to the Theory_Data Hipster_Rules. *)
fun setup_exploration const_nms thy0 =
    let
      val ctxt = Proof_Context.init_global thy0
      val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")
                       handle _ => []) const_nms
      val res_ctxt = proof_loop ctxt facts (hipspec_explore ctxt const_nms)
    in
      Library.foldl 
        (fn (thy,thm) => Context.theory_map (Hipster_Rules.add_thm thm) thy) 
        (thy0, ThyExpl_Data.proved_of_ctxt res_ctxt)
    end;

(* A tactic which picks up the constants from a subgoal, and applies theory exploration on these
   The aim is to find lemma(s) which allows for the goal to be proved. *)
fun explore_goal ctxt const_nms thm =
     let
      val thy = Proof_Context.theory_of ctxt
      (*val const_nms = Hipster_Utils.thy_consts_of (Context.theory_name (Thm.theory_of_thm thm)) thm *)
          (* FIXME: No simps for constant symbols, e.g. datatype constructors.
             FIXME: Won't pick up all the simps it needs, e.g. from functions defined in terms of *)
      val facts_nms = map (fn c => c^".simps") const_nms
      val facts = maps (fn nm => Sledgehammer_Util.thms_of_name ctxt nm 
                                 handle _ => []) facts_nms 
      val res_ctxt = proof_loop_w_prio ctxt facts (SOME thm) (hipspec_explore ctxt const_nms)
    in
      case res_ctxt of
        NONE => 
        let val _ = Output.urgent_message ("Failed to find lemmas which will prove goal.")
        in no_tac thm end
      | SOME ctxt' => (* Success, provided the explored lemmas, the thm can be proved by metis *)
        let
          val tac_str = Expl_Tacs.final_tactic_str ctxt' facts_nms
          val lemmas = Library.space_implode "\n\n"
                       (map (mk_lemma_str ctxt') 
                           (map (fn thm => (thm, tac_str)) (ThyExpl_Data.proved_of_ctxt ctxt')))
          val str_of_thm = (Sledgehammer_Util.with_vanilla_print_mode Syntax.string_of_term ctxt')
                             (Thm.concl_of thm)
          val _ = Output.urgent_message 
                    ("Try first proving lemmas:\n\n" ^ lemmas ^ "\n\n" ^
                     "then prove the open goal "^ str_of_thm ^ " " ^ 
                     Expl_Tacs.routine_tac_str)
        in
          Seq.single thm
        end
    end;


end

structure Hipster_Explore = Hipster_Explore_Fun(Simp_Metis_Tacs);
structure Hipster_Explore_Simp = Hipster_Explore_Fun(Simp_Tacs);
