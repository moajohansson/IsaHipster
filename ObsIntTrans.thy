theory ObsIntTrans
  imports Main  "~~/src/HOL/Library/Code_Target_Int"
begin
(* Workaround to translate Isabelle int to Haskell Prelude.Int
  so observer functions defined in Isabelle are translated correctly
  to Haskell *)
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
    
(* More functions may be necessary to define more kinds of observer functions,
   this is sufficient for now *)    
    
end    