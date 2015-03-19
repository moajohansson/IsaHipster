theory Pals

imports Main
        "../Listing"
        "../Sorting"
begin

datatype 'a DubL = Nil | Sing 'a | FrontBack 'a "'a DubL" 'a

fun is_pal :: "'a DubL \<Rightarrow> bool" where
  "is_pal Nil = True"
| "is_pal (Sing x) = True"
| "is_pal (FrontBack t xs r) = (t = r \<and> is_pal xs)"

fun lenD :: "'a DubL \<Rightarrow> Nat" where
  "lenD Nil = Z"
| "lenD (Sing x) = S Z"
| "lenD (FrontBack _ xs _) = S (S (lenD xs))"

fun revD :: "'a DubL \<Rightarrow> 'a DubL" where
  "revD Nil = Nil"
| "revD (Sing x) = Sing x"
| "revD (FrontBack t xs r) = FrontBack r (revD xs) t"

fun lastD :: "'a DubL \<Rightarrow> 'a" where
  "lastD (Sing t) = t"
| "lastD (FrontBack x ts y) = y"

fun headD :: "'a DubL \<Rightarrow> 'a" where
  "headD (Sing t) = t"
| "headD (FrontBack x ts y) = x"




(*
lemma lenApp: "len (app xs ts) = add (len xs) (len ts)" by hipster_induct_simp_metis
lemma addId: "add n Z = n"                              by hipster_induct_simp_metis
lemma addS2: "add n (S m) = S (add n m)"                by hipster_induct_simp_metis

lemma revLen : "len (rev xs) = len xs"
by (hipster_induct_schemes lenApp addId addS2)

lemma revDLen : "lenD (revD ts) = lenD ts"
by hipster_induct_simp_metis
lemma lastCons: "ts \<noteq> Listing.Nil \<Longrightarrow> last (Cons t ts) = last ts"
by (metis List.exhaust Listing.last.simps(2))

lemma lastElemIsLast: "last (app ts (Cons t Listing.Nil)) = t"
apply(induction ts)
apply(simp_all)
by (metis List.exhaust Listing.last.simps(2) app.simps)

lemma lastElemIsLastR: "last (app ts (Cons t Listing.Nil)) = t"
(* apply(induction ts rule: last.induct)  apply(simp_all) *)
by (hipster_induct_schemes)

lemma firstLast: "ts \<noteq> Listing.Nil \<Longrightarrow> head ts = last (rev ts)"
(* apply(induction ts)  by (simp_all add: lastElemIsLast) *)
by (metis Listing.rev.simps(2) head.cases head.simps lastElemIsLast)

lemma firstLastD: "ts \<noteq> Nil \<Longrightarrow> headD ts = lastD (revD ts)"
by (tactic {*ALLGOALS( Hipster_Tacs.timed_metis_tac @{context} @{thms
      headD.simps is_pal.elims(2) is_pal.elims(3) lastD.simps revD.simps}) *})
*)


(*
fun dropD :: "Nat \<Rightarrow> 'a DubL \<Rightarrow> 'a DubL" where
  "dropD _ Nil = Nil"
| "dropD Z ts  = ts"
| "dropD (S n) (Sing _) = Nil"
| "dropD (S n) (FrontBack x Nil y) = dropD n (Sing y)"
| "dropD (S n) (FrontBack x ts y)  = *)
(*
fun appD :: "'a DubL \<Rightarrow> 'a DubL \<Rightarrow> 'a DubL" where
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
