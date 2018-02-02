theory To_Llist
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
begin
  
fun to_llist :: "'a list \<Rightarrow> 'a Llist" where
  "to_llist [] = LNil"
| "to_llist (Cons x xs) = LCons x (to_llist xs)"
  
(*cohipster to_llist
Finds nothing interesting*)  
end  