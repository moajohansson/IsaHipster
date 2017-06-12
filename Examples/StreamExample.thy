theory StreamExample
imports Main "$HIPSTER_HOME/IsaHipster" "~~/src/HOL/Library/Code_Target_Int"
begin
  
code_printing
  type_constructor int \<rightharpoonup> (Haskell) "Prelude.Int"
  | constant "int_of_integer :: integer \<Rightarrow> _"  \<rightharpoonup> (Haskell) "Prelude.fromInteger"
  | constant "0::int" \<rightharpoonup> (Haskell) "!(0/ ::/ Prelude.Int)"
  | constant "1::int" \<rightharpoonup> (Haskell) "!(1/ ::/ Prelude.Int)"
  | constant "1" \<rightharpoonup> (Haskell) "!(1/ ::/ Prelude.Int)"
  | constant "plus :: int \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup> (Haskell) infixl 6 "+"
  | constant "uminus :: int \<Rightarrow> _" \<rightharpoonup> (Haskell) "negate"
  | constant "minus :: int \<Rightarrow> _" \<rightharpoonup> (Haskell) infixl 6 "-"
  | constant "times :: int \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup> (Haskell) infixl 7 "*"
  | constant "HOL.equal :: int \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="
  | constant "less_eq :: int \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "<="
  | constant "less :: int \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "<"
  | constant "abs :: int \<Rightarrow> _" \<rightharpoonup> (Haskell) "Prelude.abs"
  | class_instance int :: equal \<rightharpoonup> (Haskell) -


 

codatatype (sset:'a) Sstream =
SCons (shd:'a) (stl: "'a Sstream")
for
  map: smap
  rel: stream_all2

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Sstream" where
  "unfold_stream g1 g2 a = SCons (g1 a) (unfold_stream g1 g2 (g2 a))"

primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Sstream" where
"siterate g x = SCons x (siterate g (g x))"

primcorec szip where
  "shd (szip s1 s2) = (shd s1, shd s2)"
| "stl (szip s1 s2) = szip (stl s1) (stl s2)"  

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
lemma "\<exists>(n::integer). n < 0"  
  using neg_less_0_iff_less zero_less_one by blast
lemma integerz [simp]: "(\<forall>(n::integer). \<not> n \<le> 0) \<Longrightarrow> False"
  by blast
fun obsStream :: "int \<Rightarrow> 'a Sstream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"


  
print_codeproc
code_thms obsStream
(*fun obsStream :: "Code_Numeral.natural \<Rightarrow> 'a Sstream \<Rightarrow> 'a Lst" where
"obsStream 0 s = Emp" |
"obsStream (Suc n) s = Cons (shd s) (obsStream n (stl s))"*)
(*hipster unfold_stream shd stl obsStream*)
hipster_obs Sstream Lst obsStream unfold_stream shd stl

thm Sstream.coinduct
thm Sstream.coinduct_strong  
  

lemma unfold_stream_ltl_unroll:
  "unfold_stream SHD STL (STL b) = unfold_stream (SHD \<circ> STL) STL b"
apply (tactic {* Coind_Tacs.coinduct_and_sledgehammer @{context} *})
  done
    
lemma smap_unfold_stream:
  "smap f (unfold_stream SHD STL b) = unfold_stream (f \<circ> SHD) STL b"
by (tactic {* Coind_Tacs.coinduct_and_sledgehammer @{context} *})
    
lemma unfold_stream_id: "unfold_stream shd stl xs = xs"
by (tactic {* Coind_Tacs.coinduct_and_sledgehammer @{context} *})

lemma szip_iterates:
  "szip (siterate f a) (siterate g b) = siterate (map_prod f g) (a, b)"
by (tactic {* Coind_Tacs.coinduct_and_sledgehammer @{context} *})

end