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
               val (new_nm, ctxt') = ThyExpl_Data.fresh_name ctxt (*"lemma_a" (#used_thm_names q)   *)                             (* Thm used by simp need to be lifted so it use meta-variables *)
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


fun proof_loop ctxt facts cand_lemmas_str =
    let 
      val ctxt' = ThyExpl_Data.init_expl ctxt facts 
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


(* 'const_nms' are the name of the constants we wish to include in the Haskell 
   file. They must be prefixed by the theory name. *)   
fun hipspec_explore ctxt const_nms =
    let
      val thy = Proof_Context.theory_of ctxt
      val thynm = Context.theory_name thy
      val outfile = Hipster_Setup.filepath^ (Context.theory_name thy) ^"_hipspec.hs";
      val add_funs = List.foldl (fn (nm,s) => "--extra-trans "^(Long_Name.base_name nm)^ " "^s) " " const_nms;
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
                                                                   
(* Outputs snippets of proof script with the discovered lemmas that can be pasted into the theory file. *)
fun explore ctxt const_nms =
    let
      val facts_nms = map (fn c => c^".simps") const_nms
      val facts = maps (fn n => Sledgehammer_Util.thms_of_name ctxt n) facts_nms
      val tac_str = Expl_Tacs.final_tactic_str ctxt facts_nms
                        
      val res_ctxt = proof_loop ctxt facts (hipspec_explore ctxt const_nms)
      val output = Library.space_implode "\n\n"
                     ((map (mk_lemma_str ctxt) 
                           (map (fn thm => (thm, tac_str)) (ThyExpl_Data.proved_of_ctxt res_ctxt)) 
                      @ (map (mk_lemma_str ctxt) 
                             (map (fn conj => (conj,"oops")) (ThyExpl_Data.failed_of_ctxt res_ctxt)))))
    in
       (Sledgehammer_Util.with_vanilla_print_mode Output.urgent_message) 
         (Active.sendback_markup [Markup.padding_command] output)
    end;



(* A function which can be wrapped in Isabelle's setup command from a theory file.
   It adds the discovered lemmas to the Theory_Data Hipster_Rules. *)
fun setup_exploration const_nms thy0 =
    let
      val ctxt = Proof_Context.init_global thy0
      val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) const_nms
      val res_ctxt = proof_loop ctxt facts (hipspec_explore ctxt const_nms)
    in
      Library.foldl 
        (fn (thy,thm) => Context.theory_map (Hipster_Rules.add_thm thm) thy) 
        (thy0, ThyExpl_Data.proved_of_ctxt res_ctxt)
    end;


end

structure Hipster_Explore = Hipster_Explore_Fun(Simp_Metis_Tacs);
