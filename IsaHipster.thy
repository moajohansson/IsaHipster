theory IsaHipster
imports Main
begin

ML{*
structure HipsterRules = Named_Thms
(val name = @{binding "hipster_thms"} 
 val description = "Theorems discovered by theory exploration")
*}

setup {* HipsterRules.setup;*}
ML_file "ProofTools.ML"
ML_file "HipSpec.ML"


end
