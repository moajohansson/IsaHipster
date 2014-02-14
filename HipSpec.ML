(* Call HipSpec from Isabelle *)

structure HipSpec =
struct




(* Get info about Isabelle and Haskell names of constants *)
fun compute_renamings thy const_nms =
    let
      val thynm = Context.theory_name thy
       (* Note: currently assumes conjecture only contains user-defined functions. Functions that gets
       mapped to library functions get NONE in the below list. *)
      val (_,opt_list) = Code_Target.produce_code thy const_nms "Haskell" NONE thynm [];
      val renamings = map_filter 
                        (fn (isanm,hsnm) => case hsnm of 
                                              NONE => NONE 
                                            | SOME nm => SOME(isanm, Long_Name.base_name nm)) 
                                 (const_nms~~opt_list) 
    in
      renamings
    end;  



(* 'modulemn' is the name of the module in the generated Haskell-file. Its the same as the thy  *)
(* 'const_nms' are the name of the constants we wish to include in the Haskell 
   file. They must be prefixed by the theory name. *)   
fun call_hipspec ctxt facts const_nms outfile hipspec_cmd = 
    let
      val thy = Proof_Context.theory_of ctxt
      val thynm = Context.theory_name thy
      (* val ctxt = (Proof_Context.init_global thy); *) (* why do we have a thy type here??? *)
      val path_opt = SOME (Path.explode Hipster_Setup.filepath);
     
      (* THINK: What if we use functions imported from other theories? Are they translated? How? *)
      val _ = Code_Target.export_code thy const_nms [((("Haskell",thynm), path_opt), [])];
      val _ = Isabelle_System.bash (Hipster_Setup.hipspecifyer_cmd ^" H "^ 
                                    Hipster_Setup.filepath^thynm^".hs " ^outfile);    
      val (result,_) = Isabelle_System.bash_output hipspec_cmd;
     in
      ProofTools.hipspec_loop ctxt facts result
    end;

(* FIXME: If we are to deal with renamings, we need to also do so when getting conjectures
back from the Haskell world *)
fun hipspec_explore ctxt facts const_nms =
    let
      val thy = Proof_Context.theory_of ctxt
    (*  val renamings = compute_renamings thy const_nms *)
      val outfile = Hipster_Setup.filepath^ (Context.theory_name thy) ^"_hipspec.hs";

      (* val add_funs = List.foldl (fn ((_,nm),s) => "--extra-trans "^nm^ " "^s) " " renamings; *)
      val add_funs = List.foldl (fn (nm,s) => "--extra-trans "^(Long_Name.base_name nm)^ " "^s) " " const_nms;
      val hipspec_cmd = "hipspec "^ "--isabelle-mode " ^ add_funs  ^ outfile ;
    in
      call_hipspec ctxt facts const_nms outfile hipspec_cmd
    end;

fun mk_output_str ctxt (lemma,tac_str) = 
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
                                                                   
(* Allows to paste in snippets of proof script with the discovered lemmas *)
fun explore ctxt const_nms =
    let
      val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) const_nms
      val (thms,_,open_conjs) = hipspec_explore ctxt facts const_nms
   
      val facts_str = (Library.space_implode " @ " 
                                             (map (fn c => "@{thms "^c^".simps}") const_nms))
      val lemmas_str = (* Library.enclose "[" "]" (Library.space_implode ", " strs) *)
          "@{thms thy_expl}"
      val tac_str = "by (tactic {* ProofTools.induct_simp_metis @{context} " 
                    ^ Library.enclose "(" ")" (facts_str ^" @ "^lemmas_str) ^" *})"
      (* FIXME: Look up which lemmas were needed in the proofs, don't want to give Metis too
       much or too little! *)
   (*   fun lemmas_strf thm = 
          let 
            val lemmas_str = (* Library.enclose "[" "]" (Library.space_implode ", " strs) *)
                "@{thms thy_expl}"
            val tac_str = "by (tactic {* ProofTools.induct_simp_metis @{context} " 
                    ^ Library.enclose "(" ")" (facts_str ^" @ "^lemmas_str) ^" *})"
          in
            (thm,tac_str)
          end 
    *)
    (*  val thms' = map lemmas_strf thms *)

      val output = Library.space_implode "\n\n"
                     ((map (mk_output_str ctxt) 
                           (map (fn thm => (thm,tac_str)) thms)) 
                      @ (map (mk_output_str ctxt) 
                             (map (fn conj => (conj,"oops")) open_conjs)))

    in
       (Sledgehammer_Util.with_vanilla_print_mode Output.urgent_message) 
         (Active.sendback_markup output)
    end;

(* A function which can be wrapped in Isabelle's setup command from a theory file.
   It should add the discovered lemmas to the Theory_Data HipsterRules. *)
fun setup_exploration const_nms thy0 =
    let
      val ctxt = Proof_Context.init_global thy0
      val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) const_nms
      val (thms,_,_) = hipspec_explore ctxt facts const_nms
    in
      Library.foldl 
        (fn (thy,thm) => Context.theory_map (Hipster_Rules.add_thm thm) thy) 
        (thy0,thms)
    end;

(*--------------------------------------------------------------------------*)
(* HipSpec as targeted to a goal, we pick up the constants from the goal    *)
(*--------------------------------------------------------------------------*)
(*
fun hipspec_goal ctxt thm =
     let
      val thy = Proof_Context.theory_of ctxt
      val const_nms = Hipster_Util.thy_consts_of (Context.theory_name (Thm.theory_of_thm thm)) thm
      val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) const_nms
      val (lemmas,ctxt',_) = hipspec_explore ctxt facts const_nms            
    in
      (* Check which of these lemmas you need to prove the goal. 
       We're looking for a set of lemmas which allows us to prove the goal
       with simp or metis, using the lemmas. simp_metis_tac*)
    end;

*)
(* Need to extract constants!*)

(* How should this work? 

In tactic mode:
1) We trigger theory exploration and store the lemmas discovered in the Theory Data.
2) We check that the proof goes through using these lemmas.
3) We Paste in another proof-command, including the auxillary lemmas it also needs to prove,
   so we don't need to do the search again.

In Exploration mode:
1) As above.
2) Paste in several lemmas in the theory file, so we don't repeat the search 
for them over and over again. I.e. can a set-up style command replace itself with text?

*)
(*
fun hipster_induct_tac ctxt const_nms thm = 
    let
      val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) const_nms
      val _ = explore ctxt const_nms
    in
      ALLGOALS (ProofTools.timed_metis_tac ctxt (facts @ (HipsterRules.get ctxt))) thm
    end;
*) 
(* ---------------------------------------------------------------------------------*)
(* Translate an Isabelle goal into a HipSpec property *)
(* ---------------------------------------------------------------------------------*)

(* Rename constants to their haskell names and make into string *)
(*fun hipspec_term renamings t =
*)
fun try_dest_eq t = 
    SOME (HOLogic.dest_eq t)
    handle TERM _ => NONE;

fun try_dest_imp t = 
     SOME (HOLogic.dest_imp t)
    handle TERM _ => NONE;

fun dest_prop (Const ("prop", _)$t) = t ;

                                      
(* Replace a substring src by dest everywhere *)
fun matchat n src s =
      (Substring.compare (Substring.substring (s, n, size src),
                          Substring.full src) = EQUAL)
      handle _ => false (* might raise Subscript *)

fun findat n src s =
      if (size s - n) < size src then NONE
      else if matchat n src s then SOME n
           else findat (n + 1) src s

fun replace src dest s = 
    let
      fun collect n = 
          if (n > String.size s)
          then []
          else
            case (findat n src s) of
              (* What remains of s is smaller than src, just get the last bit of s. *)
              NONE => [String.substring(s, n, String.size s - n)]
            | SOME ind => (* ind is the index where first match start. *)
              (* Get the stuff from n to before the match*)
              String.substring(s, n, ind - n) ::
              dest :: (* Insert the replacement string *)
              collect (ind + size src) (* Replace in the rest of the string *)
    in
      case (String.size src) of 0 => s
                       | _ => String.concat (collect 0)
    end;
(*
fun hipspec_prop_of_thm thm = 
    let
      val thy = Thm.theory_of_thm thm;
      val trm = HOLogic.dest_Trueprop (dest_prop (Thm.concl_of thm));
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm thm);

          (* FIXME: Lookup the constants in this term *)
      val renamings = Symtab.make (compute_renamings thy ["TreeDemo.map","TreeDemo.mirror"]) (*consts_of_term trm *);

      (* Note: Keys are prefixed by thynm, remove this. *)
      fun replace_renamings (isanm,hsnm) s = replace (drop_thy_nm isanm) hsnm s;
      
      (* Turn a term into a string, replacing renamed Haskell constants, first droppig references to 
       theory-names.*)    
      fun toString t = 
          Symtab.fold replace_renamings renamings 
                      (replace ((Context.theory_name thy)^".") "" (Syntax.string_of_term ctxt t));

      val hs_eq = " =:= ";
      val hs_imp = " ==> ";
      val hs_eq_True = " =:= True";
    in
    case (try_dest_eq trm) of
      SOME (lhs,rhs) => (toString lhs) ^ hs_eq ^ (toString rhs)
    | NONE => 
      (case (try_dest_imp trm) of 
            SOME (A, B) => (toString A) ^ hs_imp ^ (toString B)
          | NONE =>  (toString trm) ^ hs_eq_True)
    end;
*)

(* Dummy tactic for hipspec *)
(*fun hipspec ctxt thm = 
    let
          (* TODO: generate HipSpec property to go in Haskell file from this. *)
       val conj_str = hipspec_prop_of_thm thm;
      (*val _ = writeln (hipspec_prop_of_thm thm) *)
      val _ =  hipspec_goal ctxt [] conj_str;
    in
      Seq.single thm
    end;
*)
(*
fun mk_proof_str lemmas =
    let
      val tac_str = "ProofTools.induct_and_metis @{context}" 
*)


fun quickspec thy quickspec_cmd path modulenm const_nms = 
    let 
      val path_opt = SOME (Path.explode path);
      val outfile = path^modulenm^"_quickspec";
      val _ = Code_Target.export_code thy const_nms [((("Haskell",modulenm),path_opt),[])];
      val r (* (output,r) *) = Isabelle_System.bash (* Isabelle_System.bash_output *)
                         (quickspec_cmd ^" Q "^ path^modulenm^".hs " ^outfile^".hs;"
                          ^"ghc -threaded -fforce-recomp "^outfile^".hs;"
                          ^outfile (* ^" > "^outfile^"_result.txt" *)) ;
     in
      r
    end;

end (* struct *)

