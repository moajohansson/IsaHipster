theory bin_distrib
imports Main
        "../../IsaHipster"
begin

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

fun plus :: "Bin => Bin => Bin" where
"plus (One) y = s y"
| "plus (ZeroAnd z) (One) = s (ZeroAnd z)"
| "plus (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus z ys)"
| "plus (ZeroAnd z) (OneAnd xs) = OneAnd (plus z xs)"
| "plus (OneAnd x2) (One) = s (OneAnd x2)"
| "plus (OneAnd x2) (ZeroAnd zs) = OneAnd (plus x2 zs)"
| "plus (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus x2 ys2))"

fun times :: "Bin => Bin => Bin" where
"times (One) y = y"
| "times (ZeroAnd xs) y = ZeroAnd (times xs y)"
| "times (OneAnd ys) y = plus (ZeroAnd (times ys y)) y"

(*hipster s plus*)
lemma lemma_a [thy_expl]: "ZeroAnd x2 = plus x2 x2"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_aa [thy_expl]: "plus x2 One = s x2"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ab [thy_expl]: "s (plus x2 y2) = plus x2 (s y2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ac [thy_expl]: "plus (s x2) y2 = plus x2 (s y2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ad [thy_expl]: "plus (plus x1 x1) x1 = plus x1 (plus x1 x1)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ae [thy_expl]: "plus (s x2) (plus y2 z2) = plus (plus x2 y2) (s z2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_af [thy_expl]: "plus (s x2) (plus y2 z2) = plus (plus y2 z2) (s x2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ag [thy_expl]: "plus (plus x2 x2) (plus x2 y2) = plus (plus x2 y2) (plus x2 x2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 x2) (plus y2 x2) = plus (plus y2 x2) (plus x2 x2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_ai [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = ZeroAnd (plus y2 x2)"
by (hipster_induct_schemes s.simps plus.simps)

lemma lemma_aj [thy_expl]: "plus x1 y1 = plus y1 x1"
by (hipster_induct_schemes s.simps plus.simps)

ML {*
val has_tvar = exists_type (exists_subtype (fn TVar _ => true | _ => false)) o prop_of

fun metis_method ((override_type_encs, lam_trans), ths) ctxt facts =
  let val (schem_facts, nonschem_facts) = List.partition has_tvar facts in
     (Method.insert_tac nonschem_facts THEN'
      CHANGED_PROP o Metis_Tactic.metis_tac (these override_type_encs)
        (the_default ATP_Proof_Reconstruct.default_metis_lam_trans lam_trans) ctxt (schem_facts @ ths)) end

fun simp_all ctxt lemmas = 
    let
       (*val _ = Pretty.writeln (Pretty.block [Pretty.str "simp_all: ", pretty_thm ctxt thm])*)
       (*val _ = @{print} thm  OR @{make_string} *)
       (*val ss = map @{print} lemmas*)
       val ctxt' = Library.foldl (fn (ctxt,thm) => Simplifier.add_simp thm ctxt)
                                 (ctxt, lemmas)
    in
      (Simplifier.asm_full_simp_tac ctxt') end

fun simp_a ctxt facts i = 
       (Method.insert_tac facts i) THEN
        (PARALLEL_GOALS o ALLGOALS o Simplifier.asm_full_simp_tac) ctxt

fun simp_or_metis ctxt (facts, lemmas) = (*let val _ = Pretty.writeln (pretty_thm ctxt thm) in*)
  let
    val do_full = Hip_Tac_Ops.use_full_types ctxt
    val simp_adds = filter (hd (Hip_Tac_Ops.simp_cond ctxt)) lemmas
    val metis_adds = filter (hd (Hip_Tac_Ops.metis_cond ctxt)) (facts @ lemmas)
  in
    ALLGOALS((simp_a ctxt simp_adds) (* FIXME: both facts and lemmas? *)     (*SOLVE_TIMEOUT 2000*) 
    THEN_ALL_NEW
    ((REPEAT_ALL_NEW (metis_method ((NONE,NONE), lemmas) ctxt facts)))) (* vs: HEADGOAL in metis_methos and REPEAT here; ALLGOALS feels safer *)
  end
*}

lemma lemma_ak [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus x2 z2)"
apply(induct y2 arbitrary: x2 z2)
by (tactic {* simp_or_metis @{context} (@{thms plus.simps s.simps Bin.exhaust}, @{thms thy_expl}) *})

lemma lemma_al [thy_expl]: "plus (plus x2 y2) (plus z2 y2) = plus (plus x2 z2) (plus y2 y2)"
by (hipster_induct_schemes s.simps plus.simps)


hipster s plus times


theorem x0 :
  "!! (x :: Bin) (y :: Bin) (z :: Bin) .
     (times x (plus y z)) = (plus (times x y) (times x z))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
