(* Call HipSpec from Isabelle *)

structure HipSpec =
struct






(* Get info about Isabelle and Haskell names of constants *)
fun compute_renamings thy const_nms =
    let
       val thynm = Context.theory_name thy;

       (* Assuming everything right of . is the constant name, and the rest is theory name *)
       fun drop_thy_nm const_nm =
           Substring.string (Substring.taker (fn c => c <> #".") (Substring.full const_nm));

       (* Note: currently assumes conjecture only contains user-defined functions. Functions that gets
       mapped to library functions get NONE in the below list. *)
      val (_,opt_list) = Code_Target.produce_code thy const_nms "Haskell" NONE thynm [];
      val renamings = map_filter (fn (isanm,hsnm) => case hsnm of NONE => NONE | SOME nm => SOME(isanm, drop_thy_nm nm)) 
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
fun call_hipspec thy const_nms outfile hipspec_cmd = 
    let
      val thynm = Context.theory_name thy;
      val path_opt = SOME (Path.explode filepath);
     
      (* THINK: What if we use functions imported from other theories? Are they translated? How? *)
      val _ = Code_Target.export_code thy const_nms [((("Haskell",thynm), path_opt), [])];
               
      val r  = Isabelle_System.bash (*Isabelle_System.bash_output *)
                         (hipspecifyer_cmd ^" H "^ filepath^thynm^".hs " ^outfile^";"
                         (* ^"ghc -threaded -fforce-recomp "^outfile^";" *)
                          ^hipspec_cmd (* ^"  > "^outfile^"_result.txt" *));
     in
      r
    end;

fun hipspec_explore thy const_nms =
    let
      val renamings = compute_renamings thy const_nms
      val outfile = filepath^ (Context.theory_name thy) ^"_hipspec.hs";
      val add_funs = List.foldl (fn ((_,nm),s) => "--extra-trans "^nm^ " "^s) " " renamings;
      val hipspec_cmd = "hipspec "^ " --auto " ^ add_funs  ^ outfile ;
    in
      call_hipspec thy const_nms outfile hipspec_cmd
    end;

fun hipspec_goal thy const_nms conj =
     let
      val renamings = compute_renamings thy const_nms
      val outfile = filepath^ (Context.theory_name thy) ^"_hipspec.hs";

      (* val add_funs = List.foldl (fn ((_,nm),s) => "--extra-trans "^nm^ " "^s) " " renamings; *)
      val add_conjs = "" 
      val hipspec_cmd = "hipspec "^ " --conj " ^ add_conjs  ^ outfile ;
    in
      call_hipspec thy const_nms outfile hipspec_cmd
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
                                      


fun hipspec_prop_of_thm thm = 
    let
      val thy = Thm.theory_of_thm thm;
      val trm = HOLogic.dest_Trueprop (dest_prop (Thm.concl_of thm));
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm thm);

      val renamings = compute_renamings thy [] (*consts_of_term trm *);

      val toString = Syntax.string_of_term ctxt;
      val hs_eq = " =:= ";
      val hs_imp = " =:> ";
      val hs_eq_True = " =:= True";
    in
    case (try_dest_eq trm) of
      SOME (lhs,rhs) => (toString lhs) ^ hs_eq ^ (toString rhs)
    | NONE => 
      (case (try_dest_imp trm) of 
            SOME (A, B) => (toString A) ^ hs_imp ^ (toString B)
          | NONE =>  (toString trm) ^ hs_eq_True)
    end;


(* Dummy tactic for hipspec *)
fun hipspec thm = 
    let
      val thy = Thm.theory_of_thm thm;
          (* TODO: generate HipSpec property to go in Haskell file from this. *)
      val _ = writeln (hipspec_prop_of_thm thm)
      (*val _ =  hipspec_goal thy conj_str *);
    in
      Seq.single thm
    end;

(*
fun hipspec_goal thy hipspecifyer_cmd path modulenm const_nms goal_term = 
    let
      val path_opt = SOME (Path.explode path);
      val outfile = path^modulenm^"_hipspec";
      (* *)
      val hipspec_cmd = "hipspec " ^ outfile;
      val goal_str = "" (* Is there a way of translating so I know what names are used in Haskell?*)
      val _ = Code_Target.export_code thy const_nms [((("Haskell",modulenm),path_opt),[])];

      val r (* (output,r) *) = Isabelle_System.bash (* Isabelle_System.bash_output *)
                         (hipspecifyer_cmd ^" HG "^ goal_str ^ " " ^ path^modulenm^".hs " ^outfile^".hs;"
                          ^"ghc -threaded -fforce-recomp "^outfile^".hs;"
                          ^hipspec_cmd ^ "--explore-theory" (* ^"  > "^outfile^"_result.txt" *));
     in
      r
    end;
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

