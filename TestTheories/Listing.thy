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

  inductable_things_in_term @{theory} @{term "len b = len a \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"};
  fun reP uu = case uu of
        Var (_,t) => let val _ = @{print} "Var" in t end
      | (t$_) => let val _ = @{print} "$" in reP t end
      | (Abs (_, t, _)) => let val _ = @{print} "Abs" in t end
      | (Free (_, t)) => t; (* TODO: Bound, Const *)

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

end

