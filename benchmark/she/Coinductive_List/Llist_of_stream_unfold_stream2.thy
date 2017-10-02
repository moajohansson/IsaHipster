theory Llist_of_stream_unfold_stream2
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

primcorec llist_of_stream2 :: "'a Stream \<Rightarrow> 'a Llist"
  where "llist_of_stream2 s = LCons (shd s) (llist_of_stream2 (stl s))"
    
primcorec stream_of_llist2 :: "'a Llist \<Rightarrow> 'a Stream"
where "stream_of_llist2 l = SCons (lhd l) (stream_of_llist2 (ltl l))"   
primcorec unfold_llist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Llist" where
  "p a \<Longrightarrow> unfold_llist p f g a = LNil" |
  "_ \<Longrightarrow> unfold_llist p f g a = LCons (f a) (unfold_llist p f g (g a))"

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "unfold_stream g1 g2 a = SCons (g1 a) (unfold_stream g1 g2 (g2 a))"
  
datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"
fun obsLlist :: "int \<Rightarrow> 'a Llist \<Rightarrow> 'a Lst" where
"obsLlist n s = (if (n \<le> 0) then Emp else Cons (lhd s) (obsLlist (n - 1) (ltl s)))"
(*hipster_obs Stream Lst obsStream stream_of_llist llist_of_stream
Times out, would need an observer for the llist also but can only 
have one at a time now*)
(* hipster_obs Stream Lst obsStream stream_of_llist2
Finds nothing ? *)
(* hipster_obs Llist Lst obsLlist llist_of_stream2
This ran for a long time and returned nothing, made my computer v. slow and wonky
*)
theorem llist_of_stream_unfold_stream2:
  "llist_of_stream2 (unfold_stream shd stl x) = unfold_llist (\<lambda>_. False) shd stl x"
(*by hipster_coinduct_sledgehammer  
Metis: Failed to replay Metis proof
resynchronize: Out of sync 
Failed to apply initial proof method\<here>*)
  apply(coinduction arbitrary: x rule: Llist.coinduct_strong)
  by auto
end