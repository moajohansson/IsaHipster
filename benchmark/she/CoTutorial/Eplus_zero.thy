theory Eplus_zero
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
  
codatatype ENat = is_zero: EZ | ESuc (epred: ENat)

primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"
  
theorem eplus_zero: "eplus n EZ = n"
by hipster_coinduct_sledgehammer
end    
    