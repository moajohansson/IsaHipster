theory prop_27
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin

(*
fun len1 :: "'a List \<Rightarrow> Nat" where
  "len1 LNil = Z"
| "len1 (LCons _ as) = S (len1 as)"

fun leneq :: "NL \<Rightarrow> NL \<Rightarrow> bool" where
  "leneq a b = (len a = len b)"


fun app1 :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "app1 LNil         ts = ts"
| "app1 (LCons r rs) ts = LCons r (app1 rs ts)"

hipster_cond leneq app1 zip Listi.app leneq*)


theorem appZips  : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
(*apply(hipster_induct_schemes app.simps len.simps List.exhaust Nat.distinct)*)
(*apply hipster_induct_schemes*)
apply (hipster_induct_schemes app.simps len.simps List.exhaust Nat.exhaust)
done

end



