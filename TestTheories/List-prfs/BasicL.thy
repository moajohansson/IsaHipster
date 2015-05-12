theory BasicL
imports Main
        "../Listing"
        "../../IsaHipster"
        "../Naturals"

begin

(* FIXME: more than reversing lists, etc. deciding which scheme to start with might reside solely
    on how different some are from others: shall we start with those "different" from the structural
    one? How can we determine this? *)

(*print_rules
print_induct_rules*)
ML {* Outer_Syntax.improper_command *}
ML {* Datatype.get_info *}

(*hipster_cond notNil maps tail init len*)
lemma lemma_a [thy_expl]: "tail (maps x2 y2) = maps x2 (tail y2)"
by hipster_induct_simp_metis
(*apply(induction y2)
apply(simp_all)
done*)

lemma lemma_aa [thy_expl]: "len (maps x2 y2) = len y2"
by hipster_induct_schemes
(*apply(induction y2)
apply(simp_all)
done*)

lemma hdmap:
  "xs \<noteq> Nil ==> head (maps f xs) = f (head xs)"
  by hipster_induct_simp_metis

lemma maptl:
  "maps f (tail xs) = tail (maps f xs)"
  by hipster_induct_simp_metis

lemma map_ext: "(!!x. x : set xs --> f x = g x) ==> map f xs = map g xs"
by (induct xs) simp_all

lemma map_ident [simp]: "map (\<lambda>x. x) = (\<lambda>xs. xs)"
by (rule ext, induct_tac xs) auto

lemma map_append [simp]: "map f (xs @ ys) = map f xs @ map f ys"
by (induct xs) auto

lemma map_map [simp]: "map f (map g xs) = map (f o g) xs"
by (induct xs) auto
(*
lemma map_comp_map[simp]: "((maps f) o (maps g)) = maps(f o g)"
apply(rule ext)
apply(simp)
oops

lemma rev_map: "rev (maps f xs) = maps f (rev xs)"
by (induct xs) auto

lemma map_eq_conv[simp]: "(map f xs = map g xs) = (!x : set xs. f x = g x)"
by (induct xs) auto

lemma map_cong [fundef_cong]:
  "xs = ys ==> (!!x. x \<in> set ys ==> f x = g x) ==> map f xs = map g ys"
  by simp

lemma map_is_Nil_conv [iff]: "(map f xs = []) = (xs = [])"
by (cases xs) auto

lemma Nil_is_map_conv [iff]: "([] = map f xs) = (xs = [])"
by (cases xs) auto

lemma map_eq_Cons_conv:
 "(map f xs = y#ys) = (\<exists>z zs. xs = z#zs \<and> f z = y \<and> map f zs = ys)"
by (cases xs) auto

lemma Cons_eq_map_conv:
 "(x#xs = map f ys) = (\<exists>z zs. ys = z#zs \<and> x = f z \<and> xs = map f zs)"
by (cases ys) auto

lemmas map_eq_Cons_D = map_eq_Cons_conv [THEN iffD1]
lemmas Cons_eq_map_D = Cons_eq_map_conv [THEN iffD1]
declare map_eq_Cons_D [dest!]  Cons_eq_map_D [dest!]

lemma ex_map_conv:
  "(EX xs. ys = map f xs) = (ALL y : set ys. EX x. y = f x)"
by(induct ys, auto simp add: Cons_eq_map_conv)

lemma map_eq_imp_length_eq:
  assumes "map f xs = map g ys"
  shows "length xs = length ys"
using assms proof (induct ys arbitrary: xs)
  case Nil then show ?case by simp
next
  case (Cons y ys) then obtain z zs where xs: "xs = z # zs" by auto
  from Cons xs have "map f zs = map g ys" by simp
  moreover with Cons have "length zs = length ys" by blast
  with xs show ?case by simp
qed
  
lemma map_inj_on:
 "[| map f xs = map f ys; inj_on f (set xs Un set ys) |]
  ==> xs = ys"
apply(frule map_eq_imp_length_eq)
apply(rotate_tac -1)
apply(induct rule:list_induct2)
 apply simp
apply(simp)
apply (blast intro:sym)
done

lemma inj_on_map_eq_map:
 "inj_on f (set xs Un set ys) ==> (map f xs = map f ys) = (xs = ys)"
by(blast dest:map_inj_on)

lemma map_injective:
 "map f xs = map f ys ==> inj f ==> xs = ys"
by (induct ys arbitrary: xs) (auto dest!:injD)

lemma inj_map_eq_map[simp]: "inj f ==> (map f xs = map f ys) = (xs = ys)"
by(blast dest:map_injective)

lemma inj_mapI: "inj f ==> inj (map f)"
by (iprover dest: map_injective injD intro: inj_onI)

lemma inj_mapD: "inj (map f) ==> inj f"
apply (unfold inj_on_def, clarify)
apply (erule_tac x = "[x]" in ballE)
 apply (erule_tac x = "[y]" in ballE, simp, blast)
apply blast
done

lemma inj_map[iff]: "inj (map f) = inj f"
by (blast dest: inj_mapD intro: inj_mapI)

lemma inj_on_mapI: "inj_on f (\<Union>(set ` A)) ==> inj_on (map f) A"
apply(rule inj_onI)
apply(erule map_inj_on)
apply(blast intro:inj_onI dest:inj_onD)
done

lemma map_idI: "(!!x. x \<in> set xs ==> f x = x) ==> map f xs = xs"
by (induct xs, auto)

lemma map_fun_upd [simp]: "y \<notin> set xs ==> map (f(y:=v)) xs = map f xs"
by (induct xs) auto

lemma map_fst_zip[simp]:
  "length xs = length ys ==> map fst (zip xs ys) = xs"
by (induct rule:list_induct2, simp_all)

lemma map_snd_zip[simp]:
  "length xs = length ys ==> map snd (zip xs ys) = ys"
by (induct rule:list_induct2, simp_all)
*)
lemma map_snd_zip: "len xs = len ys \<Longrightarrow> maps snd (zip xs ys) = y"
oops

lemma lemma_ac [thy_expl]: "(Nil \<noteq> (maps x2 y2)) = (Nil \<noteq> y2)"
by hipster_induct_simp_metis (* just metis *)
(*apply(induction y2)
apply(simp_all)
done*)


(* internally goes into conditional which Hipster cannot solve right now *)
(* FIXME: we rev the list so that it doesn't get stuck in maps.induct BUT we should control this
  behaviour! \<Rightarrow> limit simp_or_metis... *)
lemma unknown01 [thy_expl]: "init (maps x y) = maps x (init y)"
(*apply(induction arbitrary: x rule: maps.induct )
apply simp_all*)
by (hipster_induct_schemes)(*
apply(induction y rule: init.induct)
apply(simp_all)
done*)

lemma auxNilIn : "init Nil = tail Nil"
by (metis init.simps tail.simps)

lemma unknown02 [thy_expl]: "init (tail x) = tail (init x)"
by hipster_induct_schemes (*
apply(induction x)
apply(simp_all)
apply(case_tac x)
apply(simp_all)
done*)

lemma unknown03 [thy_expl]: "len (init x) = len (tail x)"
by hipster_induct_schemes (*
apply(induction x)
apply(simp_all)
apply(case_tac x)
apply(simp_all)
done*)

lemma unknown04 [thy_expl]: "notNil (init x) = notNil (tail x)" (* required schemes: init.induct *)
by hipster_induct_schemes (*
apply(case_tac x)
apply(simp_all)
apply(case_tac List)
apply(simp_all)
done *)

lemma unknown04': " (Nil \<noteq> init x) = (Nil \<noteq> tail x)" (* required schemes: init.induct *)
by hipster_induct_schemes

(*
fun noNat :: "Nat List \<Rightarrow> bool" where
  "noNat l = notNil l"
fun appnat :: "Nat List \<Rightarrow> Nat List \<Rightarrow> Nat List " where
  "appnat x y = app x y"

hipster noNat appnat*)


lemma initDef: "init (app ts (Cons t Nil)) = ts"
by hipster_induct_schemes (*
apply(induction ts rule: init.induct)
apply(simp_all)
done*)

lemma lastDef: "\<not> notNil ts \<Longrightarrow> last (Cons t ts) = t"
by (hipster_induct_simp_metis Listing.notNil.simps Listing.last.simps)

lemma lastDef' : "last (Cons t Nil) = t"
by(tactic {* Tactic_Data.routine_tac @{context} *})

(* auxiliary *)
lemma noElems: "count t Nil = Z"
by simp

lemma appNil: "app ts Nil = ts"
by (hipster_induct_simp_metis Listing.app.simps )
(*
hipster_cond notNil app init*)

(* XXX: shall we try and have some reasonable decision as to which argument + function to start inducting upon?
  eg: inner-most-left-most *)
lemma initLast: "ts \<noteq> Nil \<Longrightarrow> app (init ts) (Cons (last ts) Nil) = ts"
by (hipster_induct_schemes)
(*by (hipster_induct_schemes Listing.notNil.simps Listing.init.simps Listing.app.simps Listing.last.simps)*)
(* by hipster_induct_schemes : succeeds but takes long because it tries first notNil.induct, app.induct
    and then init.induct *)(*
apply(induction ts rule: init.induct)
apply(simp_all)
done*)


lemma initCons: "notNil ts \<Longrightarrow> init (Cons t ts) = Cons t (init ts)"
by (metis init.simps(3) notNil.elims(2))
(*by (hipster_induct_simp_metis)
by (metis init.simps(3) notNil.cases)*)

lemma initApp: "notNil ts \<Longrightarrow> init (app rs ts) = app rs (init ts)"
by (hipster_induct_schemes initCons)
(* by (hipster_induct_schemes initCons : needs initCons! succeeds but takes long - tries notNil.induct
  and app.induct before last.induct... *)(*
apply(induction rs rule: init.induct)
apply(simp_all)
apply(case_tac ts)
apply(simp_all)
done*)

lemma initAppNil: "\<not> notNil ts \<Longrightarrow> init (app rs ts) = init rs"
by (hipster_induct_schemes Listing.notNil.simps Listing.app.simps Listing.init.simps appNil)
(* before: apply(induction ts rule: init.induct) apply(simp_all add: appNil) *)

lemma lastCons: "notNil ts \<Longrightarrow> last (Cons t ts) = last ts"
by (hipster_induct_simp_metis)

lemma lastApp: "notNil ts \<Longrightarrow> last (app rs ts) = last ts"
by (hipster_induct_schemes lastCons)
(* by (hipster_induct_schemes lastCons) : needs lastCons! succeeds but takes long - tries notNil.induct
  and app.induct before last.induct... XXX: check order in general! *)
(* XXX2: seems like case distinctions (maybe double inductions too) could benefit from auxiliary
    lemmas, in general *)(*
apply(induction rs rule: last.induct)
apply(simp_all)
apply(case_tac ts)
apply(simp_all)
done*)

lemma lastAppNil: "\<not> notNil ts \<Longrightarrow> last (app rs ts) = last rs"
by (hipster_induct_schemes appNil) (* needs it! *)
(*
lemma countDiff: "\<not> eqN r t \<Longrightarrow> count r (app (Cons t Nil) ts) = count r ts"
by (hipster_induct_simp_metis)*)

lemma countInc: "eqN r t \<Longrightarrow> count r (Cons t ts) = S (count r ts)"
by (hipster_induct_simp_metis)

ML {*
   fun infer_term x ctxt =
     let val (T, ctxt') = Proof_Context.inferred_param x ctxt
     in (Free (x, T), ctxt') end;
   fun bis x = Attrib.thms x ;
   fun induct_for_me ctxt xss rule i =
     let
       val (tss, ctxt') = (fold_map o fold_map) infer_term xss ctxt
       val instss = map (map (fn inst => SOME (NONE, (inst, false)))) tss;
     in Seq.map snd o Induct.induct_tac ctxt' false instss [] [] NONE (*SOME rule*) [] i end;
*}
fun drop' :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop' _ [] = []"
| "drop' 0 xs = xs"
| "drop' (Suc n) (x#xs) = drop' n xs"
(* XXX: mailing list!  But hipster_induct_simp_metis (or schemes) never work with this, regular
  List.drop which is implemented like ours or ours *)
lemma drop'Nil: "drop' n [] = []"
apply(raw_tactic {* ALLGOALS(induct_for_me @{context} [["n"]] []) *})
apply(simp_all)
done
(*by(tactic {* Tactic_Data.routine_tac @{context} *}) works too *)

(*XXX: maybe schemes will solve it when we pick the appropriate variable (type-wise) on which to
    induct?
       or does it have something to do with how the goal of a proof is set? 
  XXX: look up for a type T what T.exhaust is *)

  declare [[show_types]]
  declare [[show_sorts]]
  declare [[show_consts]]
lemma dropNil: "drop n Nil = Nil" (* XXX: check why this solves our problem... why no "unification" *)
(*by (metis drop.simps Nat.exhaust)*)
by hipster_induct_simp_metis

ML {*
  @{thm "drop.induct"};
  (Thm.concl_of @{thm "drop.induct"});
  (HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"}));
  @{term "case x of 0 \<Rightarrow> 0 | Suc y \<Rightarrow> y"};
  @{term "P y x"};
  fun reP uu = case uu of
        Var (_,t) => t
      | (t$_) => reP t
      | (Abs (_, t, _)) => t
      | (Free (_, t)) => t; (* TODO: Bound, Const *)
  val ump = binder_types (reP(HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"})));
  val tumf = fastype_of @{term "Cons Z Nil"};
  hd (tl ump) = tumf;
  fastype_of1 ([],@{term "Cons Z Nil"});
  Type.could_match(hd (tl ump), tumf);

(*typ list * term -> typ

  hd (tl ump) = Type ( *)
*}

thm drop.induct
(*thm List.rel_induct[case_names Nil Cons, {* @{thm "List.induct"} *}]*)

lemma dropMapComm: "drop n (maps f ts) = maps f (drop n ts)"
by hipster_induct_schemes (*
apply(induction ts rule: drop.induct)
apply(simp_all)
done*)

lemma takeMapCom: "take n (maps f ts) = maps f (take n ts)" (* needs schemes! *)
by hipster_induct_schemes (*
apply(induction ts rule: drop.induct) (* XXX: either works! drop.induct OR take.induct *)
apply(simp_all)
done*)

(* XXX: for now changed order \<Longrightarrow> do something about those HO objects, such as f *)
lemma mapIntersperse: "intersperse (f a) (maps f xs) = maps f (intersperse a xs)"
by hipster_induct_schemes

fun ith :: "'a List \<Rightarrow> nat \<Rightarrow> 'a" where
  "ith (Cons t ts) 0 = t"
| "ith (Cons t ts) (Suc n) = ith ts n"

fun len' :: "'a List \<Rightarrow> nat" where
  "len' Nil = 0"
| "len' (Cons t ts) = Suc (len' ts)"

lemma extens: "\<lbrakk> len' xs = len' ys ; ALL i < len' xs. ith xs i = ith ys i \<rbrakk> \<Longrightarrow> xs = ys"
(*apply hipster_induct_schemes*)

oops

fun map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b List" where
  "map' f [] = Nil"
| "map' f (t # ts) = Cons (f t) (map' f ts)"

lemma mapIth:  "map' (\<lambda>i. ith xs i) [0..<len' xs] = xs"
oops


end



