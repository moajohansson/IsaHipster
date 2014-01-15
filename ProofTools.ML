(*------------------------------------------------------------------------------------*)
(* Proof tools and tactics for induction and simplification, porting HipSpec's proof-
   loop into the Isabelle setting. *)
(*------------------------------------------------------------------------------------*)

structure ProofTools
struct

(*------------------------------------------------------------------------------------*)
(* Isabelle tactic for proving things from HipSpec *)
(*------------------------------------------------------------------------------------*)

type conjs = {open_conjs : Thm.thm list, proved : Thm.thm list};

(* Assmume get list of strings from HipSpec, which can be directly parsed as Isabelle terms*)
fun mk_conjs ctxt lemma_strs = 
    let
      val thy = Proof_Context.theory_of ctxt;
      val conjs = map (Goal.init o (Thm.cterm_of thy) o (Syntax.read_term ctxt)) lemma_strs;
    in
      
    end;


end; (* struct *)
