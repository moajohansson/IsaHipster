theory Pals

imports Main
        "../Listing"
        "../Sorting"
begin

datatype 'a openL = Stop | Sing 'a | FrontBack 'a "'a openL" 'a
(*
fun is_pal :: "'a openL \<Rightarrow> bool" where
  "is_pal Nil = True"
| "is_pal (Sing x) = True"
| "is_pal (FrontBack t xs r) = (t = r \<and> is_pal xs)"*)

fun lenD :: "'a openL \<Rightarrow> Nat" where
  "lenD Stop = Z"
| "lenD (Sing x) = S Z"
| "lenD (FrontBack _ xs _) = S (S (lenD xs))"

fun revD :: "'a openL \<Rightarrow> 'a openL" where
  "revD Stop = Stop"
| "revD (Sing x) = Sing x"
| "revD (FrontBack t xs r) = FrontBack r (revD xs) t"

fun lastD :: "'a openL \<Rightarrow> 'a" where
  "lastD (Sing t) = t"
| "lastD (FrontBack x ts y) = y"

fun headD :: "'a openL \<Rightarrow> 'a" where
  "headD (Sing t) = t"
| "headD (FrontBack x ts y) = x"


thm sorted.induct
thm List.induct
thm drop.induct
thm take.induct
thm app.induct
thm zip.induct

prf zip.induct
prf List.induct
prf last.induct
prf drop.induct

thm headD.induct
thm openL.induct
thm lastD.induct
thm List.induct
thm last.induct
thm head.induct

ML \<open>
  val t = Induct.find_inductT @{context} @{typ "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List"}
\<close>

lemma lemma_ac2 []: "leq x2 Z = lez x2" (* NB: used to be problematic *)
(*by (metis leq.elims(2) leq.simps(1) leq.simps(2) lez.simps)*)
by (hipster_induct_simp_metis)

lemma leqLeqEq : "\<lbrakk> leq r t ; leq t r \<rbrakk> \<Longrightarrow> r = t"  (* schemes ... *)
by (hipster_induct_schemes leq.simps Nat.exhaust)

lemma dropTake : "ts = app (take n ts) (drop n ts)"
by hipster_induct_schemes (*
apply(induction ts rule: take.induct)
apply(case_tac n)
apply(simp_all)
done*)

(*lemma q1 : "sorted' (qsort xs)"
*)

lemma isortIds : "sorted ts \<Longrightarrow> isort ts = ts"
by hipster_induct_schemes (* sorted.induct *)

lemma insSortInvar : "sorted ts \<Longrightarrow> sorted (insert t ts)"
apply(induction ts arbitrary: t rule: sorted.induct)
apply(simp_all)
apply(metis (full_types) sorted.simps insert.simps)
by (hipster_induct_schemes sorted.simps insert.simps  ) (* sorted.induct *)

lemma isortSorts : "sorted (isort ts)"
by (hipster_induct_simp_metis insSortInvar)

lemma isortIdsP : "sorted ts \<Longrightarrow> sorted (isort ts)"
by (metis isortSorts)

lemma isortFixes : "isort (isort ts) = isort ts"
by (metis isortSorts isortIds)

lemma insSomeInsorted : "sorted ts \<Longrightarrow> isort (insert t ts) = insert t ts"
by (hipster_induct_simp_metis isortIds insSortInvar)


lemma lastElemIsLast: "last (app ts (Cons t Nil)) = t"
apply(induction ts)
apply(simp_all)
by (metis List.exhaust Listing.last.simps(2) app.simps)

lemma lastElemIsLastR: "last (app ts (Cons t Nil)) = t"
(* apply(induction ts rule: last.induct)  apply(simp_all) *)
by (hipster_induct_schemes)

lemma firstLast: "ts \<noteq> Nil \<Longrightarrow> head ts = last (rev ts)"
(* apply(induction ts)  by (simp_all add: lastElemIsLast) *)
by (metis Listing.rev.simps(2) head.cases head.simps lastElemIsLast)

lemma firstLastD: "ts \<noteq> Stop \<Longrightarrow> headD ts = lastD (revD ts)"
by (hipster_induct_simp_metis )

(* by (metis openL.exhaust headD.simps lastD.simps revD.simps) *)

(*
by (tactic {*ALLGOALS( Hipster_Tacs.timed_metis_tac @{context} @{thms
      headD.simps is_pal.elims(2) is_pal.elims(3) lastD.simps revD.simps}) *})
*)

(*
lemma lenApp: "len (app xs ts) = add (len xs) (len ts)" by hipster_induct_simp_metis
lemma addId: "add n Z = n"                              by hipster_induct_simp_metis
lemma addS2: "add n (S m) = S (add n m)"                by hipster_induct_simp_metis

lemma revLen : "len (rev xs) = len xs"
by (hipster_induct_schemes lenApp addId addS2)

lemma revDLen : "lenD (revD ts) = lenD ts"
by hipster_induct_simp_metis
lemma lastCons: "ts \<noteq> Nil \<Longrightarrow> last (Cons t ts) = last ts"
by (metis List.exhaust Listing.last.simps(2))
*)

(*
fun dropD :: "Nat \<Rightarrow> 'a openL \<Rightarrow> 'a openL" where
  "dropD _ Nil = Nil"
| "dropD Z ts  = ts"
| "dropD (S n) (Sing _) = Nil"
| "dropD (S n) (FrontBack x Nil y) = dropD n (Sing y)"
| "dropD (S n) (FrontBack x ts y)  = *)
(*
fun appD :: "'a openL \<Rightarrow> 'a openL \<Rightarrow> 'a openL" where
  "appD Nil ts = ts"
| "appD ts Nil = ts"
| "appD (Sing x) (Sing y) = FrontBack x Nil y"
| "appD (Sing x) (FrontBack t ys r) = FrontBack x (appD (Sing t) ys) r"
| "appD (FrontBack t ys r) (Sing x) = FrontBack t (appD ys (Sing r)) x"
| "appD (FrontBack t ys r) (FrontBack a xs b) = FrontBack t (appD (appD ys (Sing r)) (appD (Sing a) xs)) b"*)

(*| "appD (FrontBack t ys r) (Sing x) = FrontBack t (appD ys (Sing r)) x"
(appD (Sing t) ys
*)
end
