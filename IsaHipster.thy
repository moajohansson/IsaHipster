theory IsaHipster
imports Main
keywords "hipster" "hipster_cond" :: thy_decl

begin

 
ML{*
structure Hipster_Setup =
struct

<<<<<<< HEAD

(* Set the basepath to Hipster's home directory *)
val basepath = "$HIPSTER_HOME";
=======
(* FIXME: Default to Isabelle Contrib or something more sensible *)
(* Set these to your path to the Hipster directory *)
	val basepath = "~/Field/IsaHipster/";
>>>>>>> b6ad6673d5b5e1ca2a77f72a85a6c1df79e627c4
val filepath = basepath^"GenCode/";

end
*}

ML {*
structure Hipster_Rules = Named_Thms
(val name = @{binding "thy_expl"} 
 val description = "Theorems discovered by theory exploration")
*}
ML{*
(* A flag which tells Hipster that it should disregard equations
   which *only* feature functions defined in another theory, i.e. a library. *)
val thy_interesting = Attrib.setup_config_bool @{binding thy_interesting} (K true)
*}

setup {* Hipster_Rules.setup;*}

ML_file "HipsterUtils.ML"
ML_file "SchemeInstances.ML"
ML_file "ThyExplData.ML"
ML_file "HipsterTacs.ML"

ML_file "HipTacOps.ML"
ML_file "IndTacs.ML"

ML_file "TacticData.ML"
ML_file "HipsterExplore.ML"
ML_file "HipsterIsar.ML"


method_setup hipster_induct_simp = {*
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (Ind_Tacs.induct_simp_tac ctxt)))
   *}

method_setup hipster_induct_simp_metis = {*
  Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD 
      (Ind_Tacs.induct_simp_metis ctxt thms))
 *}


method_setup hipster_induct_schemes = {*
  Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD 
      (Ind_Tacs.induct_with_schemes ctxt thms))
 *}

(*
ML{*
Method.setup;

*}


method_setup hipster_goal = {*
  
*}
*)
(* 
(* Default value for tactics is induct_simp_metis.
   Use setup command to change to other hard/routine tactics.
*)
setup{* 
Tactic_Data.set_induct_simp_metis;
*}


*)


end
