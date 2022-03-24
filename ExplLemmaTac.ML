(*  Author:     Moa Johansson, Chalmers University of Technology

Lemma discovery in a proof attempt by theory exploration.

*)

structure Expl_Lemma_Tac  =
struct

(*-----------------------------------------------------------------------------------------*)
(* Theory exporation from an ongoing proof: Find lemmas to solve this subgoal              *)
(*-----------------------------------------------------------------------------------------*)

(* Tactic to check if a goal is solvable by the given lemma. *)
fun solve_goal_by_lemma_ctac lemma i (ctxt0,thm) =
  let
    (* Generalise lemma to get version with meta-variables instead. *)
    val gen_lemma = Drule.generalize (Hipster_Utils.frees_and_tfrees_of_thm lemma) lemma
    val ctxt = Simplifier.add_simp gen_lemma ctxt0
  in  
  Seq.map
    (fn (ctxt',thm') => ((Lemma_Data.set_lemma_ctxt (SOME lemma) ctxt')
                         |> Lemma_Data.set_goal_tac_ctxt ("simp[" ^ Library.string_of_int i ^ "]"), thm'))                                     
     (CTac.AS_CTACTIC (SOLVED' (Simplifier.asm_full_simp_tac ctxt) i) (ctxt,thm))
 end

(* A tactic which picks up the constants from a subgoal, and applies theory exploration on these
   The aim is to find lemma(s) which allows for the goal to be proved. *)
fun explore_goal ctxt const_nms i thm =
  let
      val conjs = Hipster_Explore.tipspec_explore ctxt NONE false const_nms
      val res_ctxt = Hipster_Explore.proof_loop ctxt conjs
     
      (*val _ = Hipster_Utils.maybe_print ctxt 100 ("End of proof loop.") *)
      val proved_lemmas =   ThyExpl_Data.proved_of_ctxt res_ctxt
      val _ = map @{print} proved_lemmas;            
      val result = CTac.SINGLE (CTac.FIRST 
                                  (map (fn l => solve_goal_by_lemma_ctac l i) proved_lemmas)) 
                  (ctxt,thm);
  in  case result of 
            NONE => Seq.empty
          | SOME (ctxt1, thm1) => 
            if (Thm.no_prems thm1) then  (* proved thm, no subgoals *)
              let val _ = writeln (Active.sendback_markup_command
                                         (Lemma_Data.mk_proof_str_w_lemma ctxt1))
              in Seq.single thm1 end
              else Seq.empty 
  end;

fun expl_goal_tac ctxt thm = 
  let
    (*val consts1 = map fst (Hipster_Utils.thy_consts_of "dummy" thm)*)
    val consts = ["app"] (* Note strip names of functions in this theory *)
    fun get_const_name ctxt c =
          c |> Proof_Context.read_const {proper = true, strict = false} ctxt  (*false dummyT *)
            |> dest_Const
            |> fst
    val const_nms = map (get_const_name ctxt) consts
    (*val _ = map @{print} consts1*)
  in  HEADGOAL (explore_goal ctxt const_nms) thm end;
end;