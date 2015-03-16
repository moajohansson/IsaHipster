(* Call the HipSpec theory exploration system. Prove the resulting conjectures. Those provable by 
   routine reasoning are deemed non-interesting and discarded. Those requiring "hard" reasoning are
   kept. *)

structure Hipster_Explore = 
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
      if length ( ThyExpl_Data.proved_of_ctxt ctxt) > 10 then SOME (ctxt |> ThyExpl_Data.set_open_conjs_ctxt cs
                                                                         |> ThyExpl_Data.add_failed_ctxt c)
                                                         else
         if (length (snd (Hipster_Utils.frees_and_tfrees_of_thm c)) > 2) then ctxt |> ThyExpl_Data.set_open_conjs_ctxt cs
                                                                   |> ThyExpl_Data.add_failed_ctxt c
                                                                   |> try_nxt_conj
                                                         else
      let 
        val r = SINGLE (Tactic_Data.routine_tac ctxt) c
        val lemma_str = (Syntax.string_of_term ctxt (Thm.concl_of c))
        (* XXX: why concl_of and not prop_of?
                FOUND: for it to be thm in type at this stage the form is: a \<Longrightarrow> #(a) *)
      in
      case r of (* Discard this, it is trivial *)
        SOME _ =>
        let
          (*TODO: uninformative, only to track ==> to be removed*)
          val _ = Pretty.writeln (Pretty.block [Pretty.str "Trivial proof: ", Pretty.str lemma_str])
        in SOME (ThyExpl_Data.set_open_conjs_ctxt cs ctxt)
        end
      | NONE =>
        let
          val res = SINGLE (Tactic_Data.hard_tac ctxt) c
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
               (* TODO: remove final_str and its printing in the message - debugging *)
               val final_str = (Syntax.string_of_term ctxt (Thm.prop_of final_thm))
               val _ = (Sledgehammer_Util.with_vanilla_print_mode Output.urgent_message)
                 ("Proved: " ^ lemma_str ^ "; Saving to ThyExpl_Data: " ^ final_str)
             in
               SOME (ctxt'
                       |> ThyExpl_Data.set_open_conjs_ctxt cs
                       |> ThyExpl_Data.add_proved_ctxt final_thm
                       |> ThyExpl_Data.set_progress_ctxt true)
             end
           (* NONE indicates that the tactic failed to prove c *)
           | NONE =>
             let
               val _ = Pretty.writeln (Pretty.block [Pretty.str "Failed proving: ", Pretty.str lemma_str])
             in 
               SOME (ctxt
                       |> ThyExpl_Data.set_open_conjs_ctxt cs
                       |> ThyExpl_Data.add_failed_ctxt c)
             end
          )
        end
      end;

fun try_prove_priority_goal ctxt goal =
    let
      val res = SINGLE (Tactic_Data.routine_tac ctxt) goal 
    in 
      case res of
        SOME _ => 
        let
        val _ = Output.urgent_message "Proved prio goal";
        in
            SOME (ThyExpl_Data.set_priority_goal_ctxt NONE ctxt)
        end
      | NONE => NONE
    end;

fun proof_loop_w_prio ctxt facts fact_nms prio_goal_opt cand_lemmas_str =
    let 
      val ctxt' = ThyExpl_Data.init_expl ctxt facts fact_nms prio_goal_opt
                                          (Library.split_lines (Library.trim_line cand_lemmas_str))     
      fun recf ctxt = 
          case (try_nxt_conj ctxt) of
            NONE => NONE (*ctxt *) (* No more lemmas to prove, not proved prio goal, fail. *)
          | SOME ctxt1 => 
            (case (ThyExpl_Data.priority_goal_of_ctxt ctxt1)
              of NONE =>  NONE (* There is no prio goals, so nothing to do! *)
            | SOME goal => 
              (case (try_prove_priority_goal ctxt1 goal) of
                 NONE => recf ctxt1
               | SOME ctxt2 => SOME ctxt2) (* Proved the priority goal, we're done! *)
            )
    in
      recf ctxt'
    end

fun proof_loop ctxt facts fact_nms cand_lemmas_str = 
     let 
      val ctxt' = ThyExpl_Data.init_expl ctxt facts fact_nms NONE
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

(* TODO: Implement properly. This is for mapping back to Isabelle constants those things that the
 code generator renamnes in Haskell. Otherwise, Isabelle will not understand the resulting lemmas. *)
val haskell_consts = [("List.rev","reverse"),("List.append","++"),
                      ("Groups.plus_class.plus", "plus_nat"), ("Groups.zero_class.zero", "Zero_nat"),
                      ("Groups.one_class.one", "one_nat")]

fun map_to_haskell isa_nm = 
    case (Library.find_first (fn (nm,_) => nm=isa_nm) haskell_consts)
         of NONE => isa_nm
          | SOME (_,hask_nm) => hask_nm;

 (* Do we always want to have the --extra-trans flag? this means extra funs gets picked up, if they
         are in the def of any of the given const-nms *)  
fun hipspec_plain consts file =
    let 
      val add_funs = List.foldl (fn (nm,s) => "--extra-trans "^(Long_Name.base_name nm)^ " "^s) " " consts
    in
      "hipspec "^ "--isabelle-mode " ^ add_funs  ^ file
    end;

(* FIXME: make cond-count a proper parameter controlled by user. *)
fun hipspec_cond cond_name consts file = 
    let 
      val add_funs = List.foldl (fn (nm,s) => "--extra-trans "^(Long_Name.base_name nm)^ " "^s) " " consts
    in
      "hipspec "^ "--isabelle-mode " ^ add_funs  ^ file ^ " --cond-name=" ^ (Long_Name.base_name cond_name) ^ " --cond-count=3" 
    end;

(* 'const_nms' are the name of the constants we wish to include in the Haskell 
   file. They must be prefixed by the theory name. *)   
fun hipspec_explore ctxt cond_opt const_nms =
    let
      val thy = Proof_Context.theory_of ctxt
      val thynm = Context.theory_name thy
      val outfile = Hipster_Setup.filepath^ (Context.theory_name thy) ^"_hipspec.hs"
      val const_nms' = map map_to_haskell const_nms
                                                            
      val hipspec_cmd = case cond_opt of NONE => hipspec_plain const_nms' outfile 
                                       | SOME c => hipspec_cond c const_nms' outfile
      val path_opt = SOME (Path.explode Hipster_Setup.filepath);    
          (* As of Isabelle2014, the below function takes a mystery boolean. Guessing false... *)
      val _ = Code_Target.export_code ctxt false const_nms [((("Haskell",thynm), path_opt), [])];
      val args = "H " ^ Hipster_Setup.filepath^thynm^".hs " ^outfile;
      val _ = Pretty.writeln (Pretty.str (hipspec_cmd ^ " - " ^ args ));
      val _ = Isabelle_System.bash ("HipSpecifyer " ^ args) (*("ghc -e 'let xs = " ^ args ^ " in System.Environment.withArgs xs HipSpecifyer.main'");*)
    in 
      fst (Isabelle_System.bash_output hipspec_cmd)
    end;



(* The output string for each lemma discovered. *)
fun mk_lemma_str ctxt prop_extract (lemma,tac_str) = 
    let    
      (* Print variables without ? *)
      val ctxt' = Config.put show_question_marks false ctxt
      (* Disables silly Isabelle YXML markup for printing *)
      val str_of_term = Sledgehammer_Util.with_vanilla_print_mode (Syntax.string_of_term ctxt')
      val lemma_str = Library.quote (str_of_term (prop_extract lemma))
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
fun explore' cond_opt ctxt const_nms =
    let
      val fact_nms = map (fn c => c^".simps") const_nms
      val facts = maps (fn n => Sledgehammer_Util.thms_of_name ctxt n
                       handle _ => []) fact_nms
                        
      val conjs = hipspec_explore ctxt cond_opt const_nms;

      val res_ctxt = proof_loop ctxt facts fact_nms conjs
      val tac_str = Tactic_Data.hard_tac_str res_ctxt 

      val output = Library.space_implode "\n\n"
                     ((map (mk_lemma_str res_ctxt Thm.prop_of) 
                           (map (fn thm => (thm, tac_str)) (ThyExpl_Data.proved_of_ctxt res_ctxt))) 
                      @ (map (mk_lemma_str res_ctxt Thm.concl_of) 
                             (map (fn conj => (conj,"oops")) (ThyExpl_Data.failed_of_ctxt res_ctxt))))
    in
      (res_ctxt, (Sledgehammer_Util.with_vanilla_print_mode Output.urgent_message) 
         (Active.sendback_markup [Markup.padding_command] output))
    end;

val explore = explore' NONE;
fun explore_cond cond = explore' cond;


(* A function which can be wrapped in Isabelle's setup command from a theory file.
   It adds the discovered lemmas to the Theory_Data Hipster_Rules. *)
fun setup_exploration const_nms thy0 =
    let
      val ctxt = Proof_Context.init_global thy0
      val fact_nms = map (fn c => c^".simps") const_nms
      val facts = maps (fn n => Sledgehammer_Util.thms_of_name ctxt n
                       handle _ => []) fact_nms
      
      val res_ctxt = proof_loop ctxt facts fact_nms (hipspec_explore ctxt NONE const_nms)
    in
      Library.foldl 
        (fn (thy,thm) => Context.theory_map (Hipster_Rules.add_thm thm) thy) 
        (thy0, ThyExpl_Data.proved_of_ctxt res_ctxt)
    end;

(* A tactic which picks up the constants from a subgoal, and applies theory exploration on these
   The aim is to find lemma(s) which allows for the goal to be proved. *)
fun explore_goal ctxt const_nms thm =
     let
      (* val thy = Proof_Context.theory_of ctxt *)
      (*val const_nms = Hipster_Utils.thy_consts_of (Context.theory_name (Thm.theory_of_thm thm)) thm *)
          (* FIXME: No simps for constant symbols, e.g. datatype constructors.
             FIXME: Won't pick up all the simps it needs, e.g. from functions defined in terms of *)
      val facts_nms = map (fn c => c^".simps") const_nms
      val facts = maps (fn nm => Sledgehammer_Util.thms_of_name ctxt nm 
                                 handle _ => []) facts_nms 
      val res_ctxt = proof_loop_w_prio ctxt facts facts_nms (SOME thm) (hipspec_explore ctxt NONE const_nms)
    in
      case res_ctxt of
        NONE => 
        let val _ = Output.urgent_message ("Failed to find lemmas which will prove goal.")
        in no_tac thm end 
      | SOME ctxt' => (* Success, provided the explored lemmas, the thm can be proved. *)
        let
          val tac_str = Tactic_Data.hard_tac_str ctxt' 
          val lemmas = Library.space_implode "\n\n"
                       (map (mk_lemma_str ctxt' Thm.prop_of)
                           (map (fn thm => (thm, tac_str)) (ThyExpl_Data.proved_of_ctxt ctxt')))
          val str_of_thm = (Sledgehammer_Util.with_vanilla_print_mode Syntax.string_of_term ctxt')
                             (Thm.concl_of thm)
          val _ = Output.urgent_message 
                    ("Try first proving lemmas:\n\n" ^ lemmas ^ "\n\n" ^
                     "then prove the open goal "^ str_of_thm ^ " " ^ 
                     (Tactic_Data.routine_tac_str ctxt'))
        in
          Seq.single thm
        end
    end;

end

