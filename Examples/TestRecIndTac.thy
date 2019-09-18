theory TestRecIndTac
  imports Main  "$HIPSTER_HOME/IsaHipster" 
begin
setup Misc_Data.set_bool_eq_split
(*setup Misc_Data.set_noisy*)

fun sorted :: "nat list \<Rightarrow> bool"
  where "sorted [] = True"
  | "sorted [x] = True"
  | "sorted (x1#x2#xs) = ((x1 \<le> x2) \<and> sorted (x2#xs))"

fun ins :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where "ins x [] = [x]"
  | "ins x (y#ys) = (if (x \<le> y) then (x#y#ys) else y#(ins x ys))"

fun isort ::  "nat list \<Rightarrow> nat list"
  where "isort [] = []"
  | "isort (x#xs) = ins x (isort xs)"



ML\<open>
(*val t = "(sorted y) \<Longrightarrow> (sorted (ins x y))";
val ctxt  =  @{context};
Variable.is_fixed ctxt "x"; 
val prop = t |> Syntax.read_prop ctxt
val thm2 = t |> Syntax.read_prop ctxt
                   |> Goal.init o (Thm.cterm_of ctxt);
val ctxt  = Variable.auto_fixes prop @{context};
val tac = Induct_CTac.recursion_induction_ctac Induct_CTac.induct_and_sledgehammer_ctac;
(* val tbad = "(\<And>x. TestRecIndTac.sorted [] \<Longrightarrow> TestRecIndTac.sorted (ins x [])) \<Longrightarrow> (\<And>x xa. TestRecIndTac.sorted [x] \<Longrightarrow> TestRecIndTac.sorted (ins xa [x])) \<Longrightarrow> (\<And>x1 x2 xs x. (\<And>x. TestRecIndTac.sorted (if x \<le> x2 then x # x2 # xs else x2 # ins x xs)) \<Longrightarrow> x1 \<le> x2 \<and> TestRecIndTac.sorted (x2 # xs) \<Longrightarrow> \<not> x \<le> x2 \<longrightarrow> TestRecIndTac.sorted (x2 # ins x xs)) \<Longrightarrow> (TestRecIndTac.sorted y \<Longrightarrow> TestRecIndTac.sorted (ins x y))"
val thm2 = t |> Syntax.read_prop ctxt
                   |> Goal.init o (Thm.cterm_of ctxt); *)
*)
\<close>
fun count :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  where
  "count x [] = 0"
| "count x (y#ys) = (if (x=y) then Suc(count x ys) else (count x ys))"
(* hipster sorted ins *)
lemma lemma_a [thy_expl]: "TestRecIndTac.sorted (ins x y) \<Longrightarrow> TestRecIndTac.sorted y"
apply (induct x y rule: TestRecIndTac.ins.induct)
apply simp
  apply simp
apply (smt TestRecIndTac.sorted.simps(2) TestRecIndTac.sorted.simps(3) dual_order.trans ins.elims)
done

lemma lemma_aa [thy_expl]: "TestRecIndTac.sorted y \<Longrightarrow> TestRecIndTac.sorted (ins x y)"
  apply (induct y arbitrary: x rule: TestRecIndTac.sorted.induct)
  apply simp
  apply simp
  apply simp
  apply presburger
  done
    
lemma lemma_ab [thy_expl]: "ins y (ins x z) = ins x (ins y z)"
  apply (induct x z arbitrary: y rule: TestRecIndTac.ins.induct)
  apply simp
apply simp
done 
ML\<open>
fun mytac ctxt = (Rec_Ind_Tacs.recinduct_simp_or_sledgehammer ctxt) ORELSE (Rec_Ind_Lemma_Spec_Tacs.koen_induct ctxt)
\<close>
method_setup recind_lemma = \<open>
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (mytac ctxt)))
\<close>
(* hipster sorted isort *)
lemma lemma_ac [thy_expl]: "TestRecIndTac.sorted (isort x)"
  apply (induct x rule: TestRecIndTac.isort.induct)
  apply simp
  apply simp
  apply (simp add: lemma_aa)
  done
    
lemma lemma_ad [thy_expl]: "isort (ins x y) = ins x (isort y)"
  apply (induct x y rule: TestRecIndTac.ins.induct)
apply simp
apply simp
using lemma_ab apply blast
  done

lemma lemma_ae [thy_expl]: "isort (isort x) = isort x"
apply (induct x rule: TestRecIndTac.isort.induct)
  apply simp
  apply simp
apply (simp add: lemma_ad)
  done

hipster count isort
lemma lemma_af [thy_expl]: "count x (ins y z) = count x (y # z)"
  apply (induct z arbitrary: x y)
  apply simp
  apply simp
  done

lemma lemma_ag [thy_expl]: "count x (isort y) = count x y"
  apply (induct y arbitrary: x)
  apply simp
  apply simp
  apply (simp add: lemma_af)
  done

end