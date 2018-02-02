theory Literate
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
begin
primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literate f x = LCons x (literate f (f x))"
end