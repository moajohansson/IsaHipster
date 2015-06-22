theory Test
imports Main
        "../Listing"

begin

lemma appZips  : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
(*apply(hipster_induct_schemes app.simps len.simps List.exhaust Nat.distinct)*)
apply(hipster_induct_schemes app.simps len.simps List.exhaust Nat.distinct)
by (tactic {* let 
      val lemmas = [] (* (ThyExpl_Data.proved_of_ctxt @{context}) @ (Hipster_Rules.get @{context})*)
      val facts = @{thms app.simps  len.simps List.exhaust Nat.distinct} in
        ALLGOALS(Ind_Tacs.induct_simp_or_metis (facts,lemmas) @{context} (SOME @{thms "zip.induct"}) (SOME ["a","b"]))
      end*})
