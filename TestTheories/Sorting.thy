theory Sorting
imports Main
        Nat
        Listing
begin

fun sorted :: "Nat List \<Rightarrow> bool" where
  "sorted Nil                   = True"
| "sorted (Cons _ Nil)          = True"
| "sorted (Cons r (Cons t ts))  = (leq r t \<and> sorted (Cons t ts))"

fun insert :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat List" where
  "insert r Nil         = Cons r Nil"
| "insert r (Cons t ts) = (if leq r t then Cons r (Cons t ts) else (Cons t (insert r ts)))"


fun isort :: "Nat List \<Rightarrow> Nat List" where
  "isort Nil = Nil"
| "isort (Cons t ts) = insert t (isort ts)"

fun qsort :: "Nat list \<Rightarrow> Nat list" where
  "qsort [] = []"
| "qsort (t # ts) = [r . r <- ts, leq r t] @ (t # [r . r <- ts, \<not> (leq r t)])"
(*
fun merge :: "Nat list \<Rightarrow> Nat list \<Rightarrow> Nat list" where
  "merge [] ts = ts"
| "merge rs [] = rs"
| "merge (r#rs) (t#ts) = (if leq r t then (r # (merge rs (t # ts)) )
                                     else (t # (merge (r # rs) ts) ) )"

fun msort :: "Nat list \<Rightarrow> Nat list" where
  "msort [] = []"
| "msort [t] = [t]"
| "msort ts = merge (msort (take ((length ts) div 2) ts))
                    (msort (drop ((length ts) div 2) ts))*)
(* in a let ... *)



(* qsort *)



end


