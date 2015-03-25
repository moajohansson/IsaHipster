theory Sorting
imports Main
        Naturals
        Listing
begin

fun sorted :: "nat List \<Rightarrow> bool" where
  "sorted Nil                   = True"
| "sorted (Cons _ Nil)          = True"
| "sorted (Cons r (Cons t ts))  = ( r \<le> t \<and> sorted (Cons t ts))"

fun insert :: "nat \<Rightarrow> nat List \<Rightarrow> nat List" where
  "insert r Nil         = Cons r Nil"
| "insert r (Cons t ts) = (if r \<le> t then Cons r (Cons t ts) else (Cons t (insert r ts)))"


fun isort :: "nat List \<Rightarrow> nat List" where
  "isort Nil = Nil"
| "isort (Cons t ts) = insert t (isort ts)"

fun qsort :: "nat list \<Rightarrow> nat list" where
  "qsort [] = []"
| "qsort (t # ts) = [r . r <- ts, r \<le> t] @ (t # [r . r <- ts, \<not> (r \<le> t)])"

fun sorted' :: "nat list \<Rightarrow> bool" where
  "sorted' []                   = True"
| "sorted' [x]         = True"
| "sorted' (r # (t # ts))  = (r \<le> t \<and>  sorted' (t # ts))"

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


