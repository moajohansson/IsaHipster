theory IsaHipster
imports Main
begin

ML{*
structure Hipster_Setup =
struct

(* FIXME: Default to Isabelle Contrib or something more sensible *)
(* Set these to your path to the Hipster directory *)
val basepath = "~/TheoremProvers/IsaHipster/";
val filepath = basepath^"GenCode/";

(* 'hipspecifyer_cmd' is the path to the HipSpecifyer executable,        *)
(*  which post-process the Haskell file so HipSpec gets generators etc.  *)

val hipspecifyer_cmd = basepath^"HipSpecifyer";

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
ML_file "ThyExplData.ML"
ML_file "HipsterTacs.ML"
ML_file "ThyExplTacs.ML"
ML_file "HipsterExplore.ML"
(*
ML_file "ProofTools.ML"
ML_file "HipSpec.ML"
*)

end
