(* Call HipSpec from Isabelle *)
use "../ProofTools.ML";

structure HipSpec =
struct


(* Assuming everything right of . is the constant name, and the rest is theory name *)
fun drop_thy_nm const_nm =
    Substring.string (Substring.taker (fn c => c <> #".") (Substring.full const_nm));



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
                                            | SOME nm => SOME(isanm, drop_thy_nm nm)) 
                                 (const_nms~~opt_list) 
    in
      renamings
    end;  


(* FIXME: Default to Isabelle Contrib or something more sensible *)
val basepath = "~/TheoremProvers/IsaHipster/";
val filepath = basepath^"GenCode/";

(* TODO: Custom Isabelle Code-generator for HipSpec, adding generators and additional imports *)
(* 'hipspecifyer_cmd' is the path to the HipSpecifyer executable                    *)
val hipspecifyer_cmd = basepath^"HipSpecifyer";

(* 'modulemn' is the name of the module in the generated Haskell-file. Its the same as the thy  *)
(* 'const_nms' are the name of the constants we wish to include in the Haskell 
   file. They must be prefixed by the theory name. *)   
fun call_hipspec ctxt const_nms outfile hipspec_cmd = 
    let
      val thy = Proof_Context.theory_of ctxt
      val thynm = Context.theory_name thy
      (* val ctxt = (Proof_Context.init_global thy); *) (* why do we have a thy type here??? *)
      val path_opt = SOME (Path.explode filepath);
     
      (* THINK: What if we use functions imported from other theories? Are they translated? How? *)
      val _ = Code_Target.export_code thy const_nms [((("Haskell",thynm), path_opt), [])];
      val _ = Isabelle_System.bash (hipspecifyer_cmd ^" H "^ filepath^thynm^".hs " ^outfile);    
      val (result,_) = Isabelle_System.bash_output hipspec_cmd;

      (* Really dodgy way of getting definfing eqs, but how do we do this otherwise??? *)
      val specs = List.foldl (fn (const,specs) => Spec_Rules.retrieve ctxt const@specs) 
                             [] (map (fn nm => Syntax.read_term ctxt nm) const_nms)
      val def_rules = 
          List.foldl (fn ((spec,(_,rules)), rs) =>
                         case spec of Spec_Rules.Equational => (rules@rs)
                                    | _ => rs)
                     [] specs
     in
      ProofTools.hipspec_loop ctxt def_rules result
    end;

fun hipspec_explore ctxt const_nms =
    let
      val thy = Proof_Context.theory_of ctxt
      val renamings = compute_renamings thy const_nms
      val outfile = filepath^ (Context.theory_name thy) ^"_hipspec.hs";

      (*val outfile = filepath^ (Context.theory_name thy) ^"_hipspec.hs"; *)
      val add_funs = List.foldl (fn ((_,nm),s) => "--extra-trans "^nm^ " "^s) " " renamings;
      val hipspec_cmd = "hipspec "^ "--isabelle-mode " ^ add_funs  ^ outfile ;
    in
      call_hipspec ctxt const_nms outfile hipspec_cmd
    end;

fun hipspec_goal ctxt const_nms conj =
     let
      val thy = Proof_Context.theory_of ctxt
      val renamings = compute_renamings thy const_nms

      val outfile = filepath^ (Context.theory_name thy) ^"_hipspec.hs";

      val add_funs = List.foldl (fn ((_,nm),s) => "--extra-trans "^nm^ " "^s) " " renamings; 
      val add_conjs = "" 
      val hipspec_cmd = "hipspec "^ " --conj " ^ add_conjs  ^ outfile ;
    in
      call_hipspec ctxt const_nms outfile hipspec_cmd
    end;

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

(* Need to extract constants!*)
fun hipspec_explore_tac ctxt const_nms thm = 
    let
      (* val thy = Thm.theory_of_thm thm; *)
      val (lemmas,_,_) =  hipspec_explore ctxt const_nms; (* Should probably return the new context too here!*)
      val facts = (maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) const_nms)
                    @ lemmas
    in
      (* Seq.single thm *)
      ALLGOALS (ProofTools.timed_metis_tac ctxt facts) thm
    end;

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

