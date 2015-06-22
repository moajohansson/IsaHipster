theory testI
imports Main
        "../IsaHipster"

begin

ML {* 
   fun infer_term x ctxt = 
     let val (T, ctxt') = Proof_Context.inferred_param x ctxt 
     in (Free (x, T), ctxt') end; 

   fun induct_tac ctxt xss rule thm = 
     let 
       val (tss, ctxt') = (fold_map o fold_map) infer_term xss ctxt; 
       val instss = map (map (fn inst => SOME (NONE, (inst, false)))) tss;
       val ress = Seq.DETERM (HEADGOAL(Induction.induction_tac ctxt' false instss [] [] (SOME rule) [])) thm;
       val ab = Seq.map snd ress
       val tt = Seq.chop 3 ress
       val _ = @{print} (Seq.list_of ress)
     in ab end; 
NO_CASES
*}


datatype 'a T1 = A1 "'a T2" | B1 
   and 'a T2 = A2 "'a T1" 

fun foo1 and foo2 where 
   "foo1 (A1 a) = foo2 a" 
| "foo1 a = a" 
| "foo2 (A2 b) = foo1 b" 

lemma 
   "foo1 (a::'a T1) = B1" 
   "foo2 (b::'a T2) = B1" 
   apply (induct a and b rule: foo1_foo2.induct)
     apply simp_all 
   done 

lemma 
   "foo1 (a::'a T1) = B1" 
   "foo2 (b::'a T2) = B1" 
   apply (raw_tactic {* induct_tac @{context} [["a"], ["b"]] @{thms foo1_foo2.induct} *})
     apply simp_all 
   done

end
