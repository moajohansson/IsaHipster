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
thm init.induct
thm last.induct
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

fun null2:: "'a List \<Rightarrow> bool" where
  "null2 Nil = True"
| "null2 _   = False"

fun rotate :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "rotate Z     xs          = xs"
| "rotate (S n) (Cons x xs) = rotate n (app xs (Cons x Nil))"
| "rotate n     Nil         = Nil"

fun intersperse :: "'a \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "intersperse x Nil = Nil"
| "intersperse x (Cons y Nil) = Cons y Nil"
| "intersperse x (Cons y ys) = Cons y (Cons x (intersperse x ys))"

fun insert :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat List" where
  "insert r Nil         = Cons r Nil"
| "insert r (Cons t ts) = (if leq r t then Cons r (Cons t ts) else (Cons t (insert r ts)))"

datatype NL = NN | NC Nat NL


(*hipster drop take app*)

(*hipster_cond notNil tail app*)

fun id :: "'a \<Rightarrow> 'a" where "id x = x"
fun remDrop :: "Nat \<Rightarrow> 'a List \<Rightarrow> Nat" where "remDrop n ts = len (drop n ts)"

lemma example : "len b = len a \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
apply(induction a b  rule: zip.induct)
apply (simp_all)
by (metis Nat.distinct(1) app.simps(1) len.simps(2) List.exhaust)

lemma eg : "maps f (init xs) = init (maps f xs)"
apply(induction f xs rule: maps.induct)
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

lemma wr : "rotate x (rotate y z) = rotate y (rotate x z)"
apply(induction x z rule: rotate.induct)
oops
hipster rotate

hipster leq add

(*hipster rotate
*)
lemma ar : " Listing.rotate (S v) (Listing.rotate x Listing.List.Nil) \<noteq> Listing.List.Nil"
oops

ML {*
fun ute hyps = map (fn t => warning (@{print} t ^ (if K false t then "eek" else "nek"))) hyps

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
  fun instance_rule (vs::vss) (_::ts) = List.concat (map (fn v => [v] :: map (fn stuff => v::stuff) (instance_rule vss ts)) vs)
    | instance_rule _ _ = []
  val nonrepR = nonreptup (ruleSets rdrop vars);
  ruleSets rdrop vars;
  ruleSets @{thm "zip.induct"} vars;
  ruleSets @{thm "app.induct"} vars;
  val vs2 = fst (inductable_things_in_term (Thm.theory_of_thm th2) (Library.nth (prems_of th2) 0));
  ruleSets rdrop vs2;
  val instanceDrop = instance_rule (ruleSets rdrop vs2) (argTyps rdrop);
  val instanceZip = instance_rule (ruleSets @{thm "zip.induct"} vars) (argTyps @{thm "zip.induct"});
  val instanceApp = instance_rule (ruleSets @{thm "app.induct"} vars) (argTyps @{thm "app.induct"});
  ruleSets @{thm "maps.induct"} vs2;
  
  
  fun var_typ_ord ((x,t1),(y,t2)) =
       (case fast_string_ord (x,y) of
          EQUAL => (if Term_Ord.typ_ord (t1,t2) = EQUAL then EQUAL else raise Type.TYPE_MATCH)
        | LESS => LESS
        | GREATER => GREATER)

  val merge_n_instances = fold (fn ws => fn bss => Ord_List.insert (dict_ord var_typ_ord) ws bss)
(*Ord_List.insert Term_Ord.term_ord t frees*) (*| indexBins v [[[]]] = [[[v]], [[]]]*)
  fun index_bins v (bin1s::bin0s::binss) =
        let val new1s = map (fn is0 => is0@[v] (*v::is0*)) bin0s
            val all1s = merge_n_instances new1s bin1s (*fold (fn ws => fn bss => Ord_List.insert (dict_ord var_typ_ord) ws bss) new1s bin1s*)
        in
           all1s :: index_bins v (bin0s::binss)
        end
    | index_bins _ [[[]]] = [[[]]]
    | index_bins _ _ = [];
  index_bins (hd vs2) ([]::(index_bins (hd vs2) [[], [[]]]));

  fun zipWith f xs ys = ListPair.foldr (fn (a, b, cs) => f(a, b)::cs) [] (xs, ys)
  val tesz = zipWith (op +) [1,2,3] [1,2];

  fun merge_bins xss yss = zipWith (fn (xs,ys) => merge_n_instances ys xs) xss yss (*(xs::xss) (ys::yss) = (xs@ys)::merge_bins xss yss*)

  fun foldl1 _ nil = raise Empty
    | foldl1 f (x::xs) = fold f xs x

  fun fix_nth_arg (t::ts) xs bins =
        let fun update_types v = map (fn t' => if Term_Ord.typ_ord (t,t') = EQUAL then snd v else t') ts
            fun into_bins v = index_bins v ([]::bins)
            val vars = filter (fn v => Type.could_match (t, snd v)) xs
            val all_bins = map (fn v => fix_nth_arg (update_types v) xs (into_bins v)) vars
       in if null all_bins then fix_nth_arg ts xs bins else foldl1 merge_bins all_bins end
    | fix_nth_arg [] _ bins = bins
  
  val tesq = fix_nth_arg (argTyps rdrop) vs2 [[[]]]
  val tesz = fix_nth_arg (argTyps @{thm "zip.induct"}) (vars) [[[]]];
  val tesa = fix_nth_arg (argTyps @{thm "app.induct"}) (vars) [[[]]];
  length tesz;
  length (nth tesz 0);
  val tesm = fix_nth_arg (argTyps @{thm "maps.induct"}) (vars) [[[]]];

*}

ML{*

val x = @{term "Nil"};
val y = @{term "S Z"};
val T = Term.type_of x;
dest_Type T;
val uu = dest_Type (Term.type_of y);
@{print} (fst uu ^ ".exhaust");
Sledgehammer_Util.thms_of_name @{context}(fst uu ^ ".exhaust");


  fun reT uu = case uu of
        Var (_,t)       => (*let val _ = @{print} "Var" in t end*) [t]
      | (t$a)           => (*let val _ = @{print} "$" in reP t end*) reT t @ reT a
      | (Abs (_, t, b)) => (*let val _ = @{print} "Abs" in t end*) t::(reT b)
      | (Free (_, t))   => [t] (* TODO: Bound, Const *)
      | Bound _         => []
      | Const (_, t)    => [t];
fun exx (args, T) = (fst o dest_Type) T :: map (fst o dest_Type) args;

val ll = distinct (op=) (List.concat (map (exx o strip_type) (distinct (op =) (reT eg2))));
fun ff tt =  not (String.isPrefix "Pure" tt orelse String.isPrefix "HOL" tt orelse String.isPrefix "prop" tt);
filter ff ll;

*}
thm Nat.exhaust
end

