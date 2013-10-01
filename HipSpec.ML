(* Call HipSpec from Isabelle *)

structure HipSpec =
struct

val filepath = "~/TheoremProvers/IsaHip/";
val hipspecifyer_cmd = filepath^"HipSpecifyer";

(* 'hipspecifyer_cmd' is the path to the HipSpecifyer executable                    *)
(* 'path' is the path to the directory where the Haskell file is generated to.      *)
(* 'modulemn' is the name of the module in the generated Haskell-file               *)
(* 'const_nms' are the name of the constants we wish to include in the Haskell 
   file. They must not be prefixed by the theory name. *)   
fun call_hipspec thy const_nms = 
    let
      val path_opt = SOME (Path.explode filepath);
      val thynm = Context.theory_name thy;
      val outfile = filepath^thynm^"_hipspec";
      (* *)
      val add_funs = List.foldl (fn (nm,s) => "--extra-trans "^nm^ " "^s) "" const_nms;
      val hipspec_cmd = "hipspec " ^ outfile ^ " --auto " ^ add_funs;
      val thy_const_nms = map (fn nm => thynm^"."^nm) const_nms;

          (* FIND OUT: Can we query Code_Target to tell us what the Haskell-names of the functions will be? *)
          (* THINK: What if we use functions imported from other theories? Are they translated? How? *)
      val _ = Code_Target.export_code thy thy_const_nms [((("Haskell",thynm), path_opt), [])];
      val (_,opt_list) = Code_Target.produce_code thy thy_const_nms "Haskell" [];
      val r  = Isabelle_System.bash (*Isabelle_System.bash_output *)
                         (hipspecifyer_cmd ^" H "^ filepath^thynm^".hs " ^outfile^".hs;"
                          ^"ghc -threaded -fforce-recomp "^outfile^".hs;"
                          ^hipspec_cmd (* ^"  > "^outfile^"_result.txt" *));
     in
      r
    end;

fun try_dest_eq t = 
    SOME (HOLogic.dest_eq t)
    handle TERM _ => NONE;

fun try_dest_imp t = 
     SOME (HOLogic.dest_imp t)
    handle TERM _ => NONE;

fun dest_prop (Const ("prop", _))$t = t 
                                      

fun hipspec_prop_of_thm thm = 
    let
      val trm = (HOLogic.dest_Trueprop(Thm.concl_of thm));
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm thm);
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
      (*val _ =  call_hipspec thy [] *)(* (hipspec_prop_of_thm thm); *)
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

