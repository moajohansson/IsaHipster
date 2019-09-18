theory IsaHipster
imports Main "$ISABELLE_HOME/src/HOL/TPTP/ATP_Problem_Import"
keywords "hipster" "hipster_cond" "cohipster" :: thy_decl

begin

 
ML\<open>

structure Hipster_Setup =
struct

(* Set these to your path to the Hipster directory *)
val basepath =
  case getenv "HIPSTER_HOME" of
    "" => let val _ = Output.warning ("Hipster: Environment variable $HIPSTER_HOME not set."^
                         "\n  Using current directory.")
          in "./" end
  | hip_home => hip_home
val filepath = basepath^"GenCode/";

(* Set these to your path to Haskell executables for HipSpec/QuickSpec/Hipspecifyer *)
val haskell_path = 
  case getenv "HASKELL_HOME" of 
    "" => let val _ = Output.warning ("Hipster: Environment variable $HASKELL_HOME not set."^
                         "\n  Using current directory.")
          in "./" end
  | haskell_home => haskell_home;
val max_term_size = "5";
val tipSpec_cmd =  haskell_path ^ "tip-spec -s " ^ max_term_size;
val tipTransl_cmd  =  haskell_path ^ "tip --hipster ";
val tipGHC_cmd =  haskell_path ^ "tip-ghc ";
end

structure Hipster_Rules = Named_Thms 
                   (val name = @{binding "thy_expl"} 
                    val description = "Theorems discovered by theory exploration");

(* A flag which tells Hipster that it should disregard equations
   which *only* feature functions defined in another theory, i.e. a library. *)
val thy_interesting = Attrib.setup_config_bool @{binding thy_interesting} (K true)

\<close>


setup \<open>Hipster_Rules.setup\<close>

ML_file "MiscData.ML"
ML_file "HipsterUtils.ML"
ML_file "InductionData.ML"
ML_file "LemmaData.ML"
ML_file "CTacs/CTac.ML"

ML_file "SledgehammerTacs.ML"
ML_file "HipTacOps.ML"
ML_file "ThyExplData.ML"
ML_file "IndTacs.ML"
ML_file "RecIndTacs.ML"
ML_file "RecIndLemmaSpecTacs.ML"

ML_file "CTacs/InductCTac.ML"
ML_file "CoIndTacs.ML"
ML_file "CoinductionData.ML"
ML_file "CTacs/CoinductCTac.ML"
  
ML_file "TacticData.ML" 
ML_file "HipsterExplore.ML"
ML_file "ExplLemmaTac.ML"

ML_file "HipsterIsar.ML"


method_setup hipster_induct_simp = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (Ind_Tacs.induct_simp_tac ctxt)))
\<close>

method_setup hipster_induct_simp_metis = \<open>
  Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD 
      (Ind_Tacs.induct_simp_metis ctxt thms))
\<close>

method_setup hipster_induct_sledgehammer = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (Ind_Tacs.induct_sledgehammer_tac ctxt)))
\<close>

method_setup hipster_recind_simp = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      ((Rec_Ind_Tacs.recinduct_simp ctxt))))
\<close>

method_setup hipster_recind = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      ((Rec_Ind_Tacs.recinduct_simp_or_sledgehammer ctxt))))
\<close>

method_setup recind_lemmaspec = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      ((Rec_Ind_Lemma_Spec_Tacs.koen_induct ctxt))))
\<close>

(* Use simp and or sledgehammer, then prints out Isar snippet using standard Isabelle tactics. *)
method_setup hipster_induct = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (Induct_CTac.hipster_induct ctxt)))
\<close>  

method_setup hipster_coinduct_sledgehammer = \<open>
  Scan.lift (Scan.succeed
    (fn ctxt => SIMPLE_METHOD
      (Coind_Tacs.coinduct_and_sledgehammer ctxt)))
\<close>

method_setup lemma_explore = \<open>
  Scan.lift (Scan.succeed
    (fn ctxt => SIMPLE_METHOD
      (Expl_Lemma_Tac.expl_goal_tac ctxt)))
\<close>
(*
ML{*
Method.setup;
*}

method_setup hipster_goal = {*
*}*)

(* 
(* Default value for tactics is induct_simp_metis.
   Use setup command to change to other hard/routine tactics.
*)
setup{* 
Tactic_Data.set_induct_simp_metis;
*}

*)


end

