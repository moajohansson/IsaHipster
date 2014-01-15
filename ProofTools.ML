(*------------------------------------------------------------------------------------*)
(* Proof tools and tactics for induction and simplification, porting HipSpec's proof-
   loop into the Isabelle setting. *)
(*------------------------------------------------------------------------------------*)


(* TODO *)
(* Grab a simpset from the current theory, how? *)
(* Remember to wrap a Trueprop before Goal.init *)

structure ProofTools =
struct

(*------------------------------------------------------------------------------------*)
(* Isabelle tactic for proving things from HipSpec *)
(*------------------------------------------------------------------------------------*)



datatype ConjQueue = ConjQ of {open_conjs : Thm.thm list, (* left to prove *)
                               failed : Thm.thm list,     (* Have tried once but failed *)
                               proved : Thm.thm list,     (* proved *)
                               simps : simpset, (* the HOL simpset + stuff we have proved *)      
                               progress : bool};          (* have we proved at least something this iteration *)

(* Apply simp to all subgoals *)
fun simp_all simpset = ALLGOALS (Simplifier.asm_full_simp_tac simpset);
 
(* Fails if all there are some subgoals left after application of simp *)
fun prove simpset conj = SOLVE (simp_all simpset) conj;



(* Assmume get list of strings from HipSpec, which can be directly parsed as Isabelle terms*)
fun mk_conjs ctxt lemma_strs = 
    let
      val thy = Proof_Context.theory_of ctxt;
          (* FIXME: Goal.init produce a mystery type-error, missing Trueprop? *)
      val conjs = map (Goal.init o (Thm.cterm_of thy) o (Syntax.read_term ctxt)) lemma_strs;
    in
      (* FIXME: Need to grab the right simpset, also containing the current theory *)
      ConjQ{open_conjs = conjs, failed = [], proved = [], simps = HOL_basic_ss, progress = false}
    end;

fun try_nxt_conj (ConjQ q) =
    case (#open_conjs q) of
      (*retry open_conjs if we have some new proved since last time.*)
      [] => if (#progress q) 
            then SOME (ConjQ{open_conjs = (#failed q),
                       failed = [],
                       proved = (#proved q),
                       simps = #simps q,
                       progress = false}) 
            else NONE

    | (c::cs) => (* try proving next open conj *) 
      let 
        val res = prove (#simps q) c;
      in
        (case Seq.pull res of 
         SOME (proved_thm, _) => 
         SOME (ConjQ{open_conjs = cs,
                     failed = (#failed q),
                     proved = proved_thm::(#proved q),
                     simps = Simplifier.add_simp proved_thm (#simps q),
                     progress = true})
       | NONE => SOME (ConjQ{open_conjs = cs,
                             failed = c::(#failed q),
                             proved = (#proved q),
                             simps = #simps q,
                             progress = #progress q})
        )
      end;

end; (* struct *)
