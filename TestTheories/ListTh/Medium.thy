theory Medium
imports "../Listing"
        "../Naturals"
        BasicL
begin

(** manual **)
lemma count01: "r \<noteq> t \<Longrightarrow> count r (app ts (Cons t Nil)) = count r ts"
apply(induction ts)
apply(simp_all)
apply(induction rule: eqN.induct)
apply(simp_all)
done

(*
lemma identityNat: "eqN x x"
apply(induction x)
apply(simp_all)
done *)

lemma count02: "count t ts = n \<Longrightarrow> count t (Cons t ts) = S n"
(* apply(case_tac ts)     (* OR: induciton ts on its own *)
by (simp_all add: identityNat) (*XXX: how come the simplifier cannot get itself to the conclusion eqN v v? *)
*)
by (hipster_induct_simp_metis)

lemma count03: "count t ts = n \<Longrightarrow> count t (app rs ts) = add (count t rs) n"
by (hipster_induct_simp_metis)

lemma elem01: "elem t ts \<Longrightarrow> elem t (Cons r ts)"
(* apply(induction ts) by (simp_all) *)
by (hipster_induct_simp_metis)

lemma elem02: "elem t ts \<Longrightarrow> elem t (app ts rs)"
(* apply(induction ts) by (simp_all) *)
by (hipster_induct_simp_metis)

lemma elem03: "elem t ts \<Longrightarrow> elem t (app rs ts)"
(* apply(induction rs)  apply(simp_all) *)
by (hipster_induct_simp_metis)

lemma inRev: "elem t ts \<Longrightarrow> elem t (rev ts)"
(* apply(induction ts)  apply(simp_all)  by (metis elem.simps(2) elem02 elem03) *)
by (hipster_induct_simp_metis elem02 elem03 elem.simps(2))

lemma lastAfterCons: "ts \<noteq> Nil \<Longrightarrow> last ts = last (Cons t ts)"
by (hipster_induct_simp_metis)

lemma lastElemIsLast: "last (app ts (Cons t Nil)) = t"
apply(induction ts rule: last.induct)
by (simp_all)

lemma firstLast: "ts \<noteq> Nil \<Longrightarrow> head ts = last (rev ts)"
(* apply(induction ts)  by (simp_all add: lastElemIsLast) *)
by (hipster_induct_simp_metis lastElemIsLast)

lemma setCountRev: "count t ts = count t (rev ts)"
apply(induction ts)  (* XXX: no need for  rule: rev.induct ! *)
by (simp_all add: count03 addId addS2) (* for some reason still won't do with hipster and these lemmas *)

lemma lenTake: "leq n (len ts) \<Longrightarrow> len (take n ts) = n"
apply(induction ts rule: take.induct)
apply(simp_all)
done

lemma lastStays: "ts \<noteq> Nil \<Longrightarrow> last ts = last (Cons t ts)"
(* apply(induction ts)  apply(simp_all) *)
by (hipster_induct_simp_metis)

lemma len0: "Z = len ts \<Longrightarrow> ts = Nil"
by (hipster_induct_simp_metis)

lemma notLen0: "leq (S n) (len ts) \<Longrightarrow> ts \<noteq> Nil"
apply(induction ts)
by (simp_all)

lemma notEmptyDrop: "leq (S n) (len ts) \<Longrightarrow> (drop n ts) \<noteq> Nil"
apply(induction ts rule: drop.induct)
by (simp_all add: notLen0)

lemma emptyDrop: "leq (len ts) n \<Longrightarrow> drop n ts = Nil"
apply(induction ts rule: drop.induct)
apply(simp_all)
apply(frule noLowerZ) (* XXX: why frule's is not done also by the simplifier? *)
by (simp_all add: len0)

lemma lastDrop : "leq (S n) (len ts) \<Longrightarrow> last (drop n ts) = last ts"
apply(induction ts rule: drop.induct)
apply(simp_all)
oops

(* TODO: strategy: start with tailing call? nah, didn't matter: both take.induct and drop.induct get us there *)
lemma dropTake : "ts = app (take n ts) (drop n ts)"
apply(induction ts rule: take.induct)
apply(case_tac n)
apply(simp_all)
(** conditional **)
done

lemma takeMore: "leq (len ts) n \<Longrightarrow> take n ts = ts"
apply(induction ts rule: take.induct)
apply(simp_all)
apply(drule emptyDrop)
by (simp_all)

lemma initAsTake: "init ts = take (sub (len ts) (S Z)) ts"
apply(induction ts rule: init.induct)
by (simp_all add: subId)


lemma zipNil: "\<not> notNil rs \<Longrightarrow> zip rs ts = Nil"
by (hipster_induct_simp_metis)

lemma zip2nil: "zip ts Nil = Nil"
apply(induction ts)
by (simp_all)

lemma zipNilBis: "\<not> notNil ts \<Longrightarrow> zip rs ts = Nil"
by (hipster_induct_simp_metis zip2nil)

lemma zipNotNil: "notNil rs \<Longrightarrow> zip (Cons t ts) rs = Cons (t, head rs) (zip ts (tail rs))"
by (hipster_induct_simp_metis)

lemma appZips: "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
apply(induction a b rule: zip.induct)
apply(simp_all)
apply(drule len0)
by (simp_all)

lemma zipSingleton: "zip (Cons t Nil) (Cons r Nil) = Cons (t,r) Nil"
by simp

lemma revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
apply(induction rs ts rule: zip.induct)
apply(simp_all)
oops

end


