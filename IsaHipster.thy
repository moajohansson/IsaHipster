theory IsaHipster
imports Main
begin

ML{*

structure HipsterNames = 
struct

val name_index = Attrib.setup_config_int @{binding "hipster_name_ind"} (K 1)
 
fun new_name thy = 
    let 
    val i = Config.get_global thy name_index
    val thy' = Config.put_global name_index (i+1) thy
    in  (thy',"hipster_lemma_"^ (Library.string_of_int i)) end;

end;
*}

ML{*
structure HipsterRules = Named_Thms
(val name = @{binding "hipster_thms"} 
 val description = "Theorems discovered by theory exploration")
*}
setup {* HipsterRules.setup;*}



ML_file "ProofTools.ML"
ML_file "HipSpec.ML"


end
