theory prop_27
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem appZips  : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
(*apply(hipster_induct_schemes app.simps len.simps List.exhaust Nat.distinct)*)
(*apply hipster_induct_schemes*)
apply (hipster_induct_schemes app.simps len.simps List.exhaust Nat.exhaust)
done

end



