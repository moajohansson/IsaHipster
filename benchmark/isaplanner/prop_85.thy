theory prop_85
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun zip2 :: "'a list => 'b list => ('a * 'b) list" where
  "zip2 (Nil2) y = Nil2"
  | "zip2 (Cons2 z x2) (Nil2) = Nil2"
  | "zip2 (Cons2 z x2) (Cons2 x3 x4) = Cons2 (z, x3) (zip2 x2 x4)"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster zip2 len append rev *)
  (*hipster rev*)
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes rev.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes rev.simps)

lemma lemma_ab [thy_expl]: "append (rev x5) (rev y5) = rev (append y5 x5)"
by (hipster_induct_schemes rev.simps)

(*hipster len zip2*)
lemma lemma_ac [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_schemes len.simps zip2.simps)

lemma lemma_ad [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_schemes len.simps zip2.simps)


(*hipster rev zip2*)
lemma lemma_ae [thy_expl]: "zip2 x2 (append x2 y2) = zip2 x2 x2"
by (hipster_induct_schemes rev.simps zip2.simps)

lemma lemma_af [thy_expl]: "zip2 (append x1 y1) x1 = zip2 x1 x1"
by (hipster_induct_schemes rev.simps zip2.simps)


(*hipster zip2 append*)
lemma lemma_ah [thy_expl]: "zip2 (append x4 x4) (Cons2 y4 Nil2) = zip2 x4 (Cons2 y4 Nil2)"
by (hipster_induct_schemes zip2.simps append.simps)

lemma lemma_ai [thy_expl]: "zip2 (Cons2 x1 Nil2) (append y1 y1) = zip2 (Cons2 x1 Nil2) y1"
by (hipster_induct_schemes zip2.simps append.simps)

(*hipster len rev append*)
lemma lemma_aj [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes len.simps rev.simps append.simps)


lemma unknown []: "zip2 (append x y) (rev x) = zip2 x (rev x)"
oops

lemma unknown []: "zip2 (rev x) (append x y) = zip2 (rev x) x"
oops

(*hipster len rev append zip2*)
(*lemma lemma_ag [thy_expl]: "len (prop_85.append x4 y4) = len (prop_85.append y4 x4)"
by (hipster_induct_schemes prop_85.len.simps prop_85.rev.simps prop_85.append.simps prop_85.zip2.simps Nat.exhaust)*)

lemma unknown []: "zip2 (prop_85.append x y) (prop_85.rev x) = zip2 x (prop_85.rev x)"
oops

lemma unknown []: "zip2 (prop_85.rev x) (prop_85.append x y) = zip2 (prop_85.rev x) x"
oops

lemma unknown []: "zip2 (prop_85.append x x) (prop_85.rev x) = zip2 x (prop_85.rev x)"
oops

lemma unknown []: "zip2 (prop_85.rev x) (prop_85.append x x) = zip2 (prop_85.rev x) x"
oops

hipster len append

fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun lenb :: "Nat list => Nat" where
  "lenb (Nil2) = Z"
  | "lenb (Cons2 y xs) = S (lenb xs)"
fun leneq :: "Nat list \<Rightarrow> Nat list \<Rightarrow> bool" where
  "leneq x y = equal2 (lenb x) (lenb y)"
  fun appendb :: "Nat list => Nat list => Nat list" where
  "appendb (Nil2) y = y"
  | "appendb (Cons2 z xs) y = Cons2 z (appendb xs y)"
  fun revb :: "Nat list => Nat list" where
  "revb (Nil2) = Nil2"
  | "revb (Cons2 y xs) = appendb (revb xs) (Cons2 y (Nil2))"

(*hipster equal2*)
lemma lemma_ag [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes prop_85.equal2.simps)

lemma lemma_ak [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_85.equal2.simps)

lemma lemma_al [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_85.equal2.simps)

(*hipster_cond equal2 len*)
lemma lemma_am [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes prop_85.equal2.simps prop_85.len.simps)

(*hipster_cond equal2 leneq len*)


(*hipster equal2 leneq appendb*)
lemma lemma_an [thy_expl]: "appendb (appendb x1 y1) z1 = appendb x1 (appendb y1 z1)"
by (hipster_induct_schemes prop_85.equal2.simps prop_85.leneq.simps prop_85.appendb.simps)

lemma lemma_ao [thy_expl]: "leneq (appendb x1 y1) (appendb x1 z1) = leneq y1 z1"
by (hipster_induct_schemes prop_85.equal2.simps prop_85.leneq.simps prop_85.appendb.simps)

lemma lemma_ap [thy_expl]: "equal2 Z (lenb x2) = leneq y2 (appendb y2 x2)"
by (hipster_induct_schemes prop_85.equal2.simps prop_85.leneq.simps prop_85.appendb.simps)

(*
hipster_cond equal2 leneq appendb

hipster_cond leneq equal2


hipster leneq equal2 lenb


hipster_cond leneq equal2 lenb

hipster_cond leneq appendb len



hipster equal2 leneq len appendb


hipster_cond equal2 leneq len appendb


hipster_cond leneq appendb revb equal2*)


lemma lemma_applen [thy_expl]: "len (append x y) = len (append y x)"
apply(induction x)
apply(simp_all)
apply(metis thy_expl append.simps len.simps list.exhaust)
by (hipster_induct_schemes append.simps len.simps list.exhaust)


lemma lemma_at [thy_expl]: "len (rev x3) = len x3"
by (hipster_induct_schemes len.simps rev.simps append.simps)

(*
len (x++y) == len (y++x) proved by induction on  y, x

zip (x++y) (rev x) == zip x (rev x) failed to be proved
zip (rev x) (x++y) == zip (rev x) x failed to be proved

zip x x++++zip y z == zip (x++y) (x++z) proved by induction on  x
22.07 s	

zip (rev x) (rev x) == prev (zip x x) proved by induction on  x
25.19 s	
prop_85 failed to be proved
25.23 s	

zip (x++y) (rev x) == zip x (rev x) failed to be proved
zip (rev x) (x++y) == zip (rev x) x failed to be proved
zip (rev x) (x++x) == zip (rev x) x failed to be proved
zip (x++x) (rev x) == zip x (rev x) failed to be proved

prop_85 failed to be proved

*)

  theorem x0 :
    "((len xs) = (len ys)) ==>
       ((zip2 (rev xs) (rev ys)) = (rev (zip2 xs ys)))"
       by (hipster_induct_schemes len.simps zip2.simps rev.simps)

(*
    apply(induction xs ys rule: zip2.induct)
apply simp_all
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
