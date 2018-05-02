theory LtakeWhile_repeat
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
primcorec ltakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "lnull xs \<or> \<not> P (lhd xs) \<Longrightarrow> lnull (ltakeWhile P xs)"
| "lhd (ltakeWhile P xs) = lhd xs"
| "ltl (ltakeWhile P xs) = ltakeWhile P (ltl xs)"
datatype ('a, 'b) Pair2 = Pair2 'a 'b 

primcorec literates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literates f x = LCons x (literates f (f x))"

primcorec repeat :: "'a \<Rightarrow> 'a Llist"
  where "repeat x = LCons x (repeat x)"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

fun obsLList :: "int \<Rightarrow> 'a Llist \<Rightarrow> 'a Lst" where
"obsLList n s = (if (n \<le> 0) then Emp else Cons (lhd s) (obsLList (n - 1) (ltl s)))"

(* hipster_obs Llist Lst obsLList ltakeWhile repeat
Nothing non-trivial found *)
theorem ltakeWhile_repeat:
  "ltakeWhile P (repeat x) = (if P x then repeat x else LNil)"
  by hipster_coinduct_sledgehammer

end