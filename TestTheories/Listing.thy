theory Listing
imports Main
        Naturals
begin

datatype 'a List = Nil | Cons 'a "'a List"

fun len :: "'a List \<Rightarrow> Nat" where
  "len Nil = Z"
| "len (Cons _ as) = S (len as)"

fun app :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "app Nil         ts = ts"
| "app (Cons r rs) ts = Cons r (app rs ts)"

fun rev :: "'a List \<Rightarrow> 'a List" where
  "rev Nil = Nil"
| "rev (Cons r ts) = app (rev ts) (Cons r Nil)"

fun qrev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "qrev Nil         a = a"
| "qrev (Cons b bs) a = qrev bs (Cons b a)"

fun take :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "take Z     _           = Nil"
| "take _     Nil         = Nil"
| "take (S n) (Cons t ts) = Cons t (take n ts)"

fun drop :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "drop Z     ts          = ts"
| "drop _     Nil         = Nil"
| "drop (S n) (Cons t ts) = drop n ts"

fun count :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat" where
  "count _ Nil = Z"
| "count n (Cons t ts) = (if eqN n t then S (count n ts) else count n ts)"

fun elem :: "Nat \<Rightarrow> Nat List \<Rightarrow> bool" where
  "elem _ Nil = False"
| "elem r (Cons t ts) = (if eqN r t then True else elem r ts)"

(* maybe remove *)
fun head :: "'a List \<Rightarrow> 'a" where
  "head (Cons t _) = t"

fun last :: "'a List \<Rightarrow> 'a" where
  "last (Cons t Nil) = t"
| "last (Cons _ ts)  = last ts"
(* till here (?) *)

fun init :: "'a List \<Rightarrow> 'a List" where
  "init Nil          = Nil"
| "init (Cons _ Nil) = Nil"
| "init (Cons t ts)  = Cons t (init ts)"

fun tail :: "'a List \<Rightarrow> 'a List" where
  "tail Nil         = Nil"
| "tail (Cons _ ts) = ts"

fun maps :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a List \<Rightarrow> 'b List" where
  "maps _ Nil = Nil"
| "maps f (Cons a as) = Cons (f a) (maps f as)"

fun zip :: "'a List \<Rightarrow> 'b List \<Rightarrow> ('a * 'b) List" where
  "zip Nil _   = Nil"
| "zip _   Nil = Nil"
| "zip (Cons t ts) (Cons r rs) = Cons (t,r) (zip ts rs)"

fun notNil :: "'a List \<Rightarrow> bool" where
  "notNil Nil = False"
| "notNil _   = True"

fun rotate :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "rotate Z     xs          = xs"
| "rotate (S n) (Cons x xs) = rotate n (app xs (Cons x Nil))"
| "rotate n     Nil         = Nil"

fun intersperse :: "'a \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "intersperse x Nil = Nil"
| "intersperse x (Cons y Nil) = Cons y Nil"
| "intersperse x (Cons y ys) = Cons y (Cons x (intersperse x ys))"

(*hipster_cond notNil tail app*)

fun id :: "'a \<Rightarrow> 'a" where "id x = x"
fun remDrop :: "Nat \<Rightarrow> 'a List \<Rightarrow> Nat" where "remDrop n ts = len (drop n ts)"

lemma example : "len b = len a \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
apply(induction a b  rule: zip.induct)
apply (simp_all)
by (metis Nat.distinct(1) app.simps(1) len.simps(2) List.exhaust)

lemma eg : "maps f (init xs) = init (maps f xs)"
apply(induction xs rule: maps.induct)
apply simp_all
(* ( {* Drule.flexflex_unique*}*)
(*apply (tactic {*  prune_params_tac @{context} *})
apply (tactic {*  flexflex_tac *})*)
proof -
  fix fa :: "'b \<Rightarrow> 'a" and a :: 'b and as :: "'b List"
  assume a1: "maps fa (init as) = init (maps fa as)"
  obtain esk1\<^sub>1 :: "'b List \<Rightarrow> 'b" and esk2\<^sub>1 :: "'b List \<Rightarrow> 'b List" where f2: "\<forall>x\<^sub>4. x\<^sub>4 = Listing.List.Cons (esk1\<^sub>1 x\<^sub>4) (esk2\<^sub>1 x\<^sub>4) \<or> x\<^sub>4 = Listing.List.Nil" by (metis head.cases)
  hence f3: "\<And>x1 x2. init (Listing.List.Cons (x1\<Colon>'b) x2) = Listing.List.Cons x1 (init x2) \<or> Listing.List.Nil = x2" by (metis init.simps(3))
  have f4: "\<And>x1 x2 x\<^sub>3 x\<^sub>4. init (Listing.List.Cons (x1\<Colon>'a) (maps x2 (Listing.List.Cons (x\<^sub>3\<Colon>'b) x\<^sub>4))) = Listing.List.Cons x1 (init (maps x2 (Listing.List.Cons x\<^sub>3 x\<^sub>4)))" by simp
  have "as = Listing.List.Nil \<longrightarrow> init (maps fa (Listing.List.Cons a as)) = maps fa (init (Listing.List.Cons a as))" by simp
  thus "maps fa (init (Listing.List.Cons a as)) = init (Listing.List.Cons (fa a) (maps fa as))" using a1 f2 f3 f4 by (metis maps.simps(2))
qed
(*by (metis head.cases init.simps(2) init.simps(3) maps.simps(1) maps.simps(2))
by (metis List.distinct(1) head.cases init.simps(2) init.simps(3) maps.elims maps.simps(1) maps.simps(2))
*)

lemma eg2 : "leq (S n) (len ts) \<Longrightarrow> (drop n ts) \<noteq> Nil"
apply (induction n ts rule: drop.induct)
apply simp_all
oops

ML {*
fun inductable_things_in_term thry t =
    let val _ = @{print} (Hipster_Utils.frees_of t)
        val _ = @{print} (Term.strip_all_vars t)
        fun lookup thy s = case (Datatype.get_info thy s) of
               NONE => NONE
             | SOME di => SOME (#induct di);
      fun datatype_chk (Type(tn,_)) = Basics.is_some (lookup thry tn)
        | datatype_chk _ = false;
    in List.partition (datatype_chk o snd) ((Hipster_Utils.frees_of t) @ (Term.strip_all_vars t)) end;

  val prop = @{term "len b = len a \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"};
  val th' = (Goal.init o (Thm.cterm_of @{theory})) ((Syntax.read_prop @{context}) "len b = len a \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)");

  inductable_things_in_term @{theory} prop;
  fun reP uu = case uu of
        Var (_,t)       => (*let val _ = @{print} "Var" in t end*) t
      | (t$_)           => (*let val _ = @{print} "$" in reP t end*) reP t
      | (Abs (_, t, _)) => (*let val _ = @{print} "Abs" in t end*) t
      | (Free (_, t))   => t; (* TODO: Bound, Const *)

  @{thm "drop.induct"};
  (Thm.concl_of @{thm "drop.induct"});
  (HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"}));
  @{term "case x of 0 \<Rightarrow> 0 | Suc y \<Rightarrow> y"};
  @{term "P y x"};
  (reP(HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"})));
  val ump = binder_types (reP(HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"})));
  val tumf = fastype_of @{term "Cons Z Nil"};
  hd (tl ump) = tumf;
  fastype_of1 ([],@{term "Cons Z Nil"});
  Type.could_match(hd (tl ump), tumf);
*}

ML {*
  val rdrop = @{thm "drop.induct"}
  val eg2 = @{term "leq (S n) (len ts) \<Longrightarrow> (drop n ts) \<noteq> Nil"}
  val th2 = (Goal.init o (Thm.cterm_of @{theory})) ((Syntax.read_prop @{context}) "leq (S n) (len ts) \<Longrightarrow> (drop n ts) \<noteq> Nil")
  fun argTyps r = binder_types (reP (HOLogic.dest_Trueprop (Thm.concl_of ( r)))) (* types of pred P args *)
  (*val _ = @{print} (prems_of th')
  val _ = @{print} (length (prems_of @{thm "len.induct"}));
  val _ = @{print}((concl_of th'));
  val bist = fst (inductable_things_in_term (Thm.theory_of_thm th') (concl_of th'))*)
  val vars = fst (inductable_things_in_term (Thm.theory_of_thm th') (Library.nth (prems_of th') 0))
  val _ = @{print} vars
  fun ruleVars r  vs = map fst (filter (fn v => exists (fn tr => Type.could_match (tr,snd v)) (argTyps r)) vs)
  fun filter_matching t vs = filter (fn v => Type.could_match (t, snd v)) vs
  fun rulSss r = map (fn t => filter_matching t vars) (argTyps r)
  fun ruleSets r vs = map (fn rv => filter (fn av => Type.could_unify (rv, snd av)) vs) (argTyps r)
  fun paired [] = []
    | paired (v::vs) = map (fn w => [v,w]) vs @ paired vs
  val indvars = map (fn v => [v]) (ruleVars rdrop vars) @ paired (ruleVars rdrop vars)
  fun nonreptup [] = []
    | nonreptup (vs:: vss) = fold (fn v => fn acc => acc @ (map (fn ts => v::ts) (nonreptup (map (filter (fn t => not (v = t))) vss)))) vs [] @ nonreptup vss
  fun instance_rule (vs::vss) (t::ts) = map 
  val nonrepR = nonreptup (ruleSets rdrop vars);
  ruleSets rdrop vars;
  ruleSets @{thm "zip.induct"} vars;
  ruleSets @{thm "app.induct"} vars;
  val vs2 = fst (inductable_things_in_term (Thm.theory_of_thm th2) (Library.nth (prems_of th2) 0));
  ruleSets rdrop vs2;
  ruleSets @{thm "maps.induct"} vs2;
*}

end

