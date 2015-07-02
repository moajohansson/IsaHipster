theory dropTake
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S Nat

fun eqN :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "eqN Z Z = True"
| "eqN (S n) (S m) = eqN n m"
| "eqN _     _     = False"

datatype 'a List = Nil | Cons 'a "'a List"

fun len :: "'a List \<Rightarrow> Nat" where
  "len Nil = Z"
| "len (Cons _ as) = S (len as)"

fun app :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "app Nil         ts = ts"
| "app (Cons r rs) ts = Cons r (app rs ts)"


fun init :: "'a List \<Rightarrow> 'a List" where
  "init Nil          = Nil"
| "init (Cons _ Nil) = Nil"
| "init (Cons t ts)  = Cons t (init ts)"

fun tail :: "'a List \<Rightarrow> 'a List" where
  "tail Nil         = Nil"
| "tail (Cons _ ts) = ts"


fun zip :: "'a List \<Rightarrow> 'b List \<Rightarrow> ('a * 'b) List" where
  "zip Nil _   = Nil"
| "zip _   Nil = Nil"
| "zip (Cons t ts) (Cons r rs) = Cons (t,r) (zip ts rs)"

lemma appZips  : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
by (hipster_induct_schemes app.simps zip.simps len.simps List.exhaust Nat.distinct)

fun take :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "take Z     _           = Nil"
| "take _     Nil         = Nil"
| "take (S n) (Cons t ts) = Cons t (take n ts)"

fun drop :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "drop Z     ts          = ts"
| "drop _     Nil         = Nil"
| "drop (S n) (Cons t ts) = drop n ts"

lemma dropTake : "ts = app (take n ts) (drop n ts)"
by (hipster_induct_schemes)

fun sub :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "sub Z _     = Z"
| "sub (S n) Z = S n"
| "sub (S n) (S m) = sub n m"

lemma initAsTake: "init ts = take (sub (len ts) (S Z)) ts"
by (hipster_induct_schemes sub.simps Nat.exhaust)


fun count :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat" where
  "count _ Nil = Z"
| "count n (Cons t ts) = (if eqN n t then S (count n ts) else count n ts)"

lemma count01: "\<not> (eqN r t) \<Longrightarrow> count r (app ts (Cons t Nil)) = count r ts"
by (hipster_induct_simp_metis)

lemma initTail : "init (tail x) = tail (init x)"
by (hipster_induct_schemes)

lemma lenInitTail: "len (init x) = len (tail x)"
by (hipster_induct_schemes)


fun notNil :: "'a List \<Rightarrow> bool" where
  "notNil Nil = False"
| "notNil _   = True"

lemma initApp: "notNil ts \<Longrightarrow> init (app rs ts) = app rs (init ts)"
by (hipster_induct_schemes notNil.elims init.simps app.simps)

end

