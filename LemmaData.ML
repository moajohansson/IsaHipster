(*  Author:     Moa Johansson, Chalmers University of Technology

To be used by tactics that can speculate some lemmas during proof, to record which 
one was successful in the proof.
*)

(*-----------------------------------------------------------------------------------------*)
structure Lemma_Data =
struct

(* Kept simple for now *)
datatype T = Data of
  { lemma : Thm.thm option,
    lemma_tac : string,
    goal_tac : string
  }

fun get_lemma (Data d) = (#lemma d);
fun get_lemma_tac (Data d) = (#lemma_tac d)
fun get_goal_tac (Data d) = (#goal_tac d)

fun update_lemma f (Data d) = Data{lemma = f (#lemma d), lemma_tac = #lemma_tac d, goal_tac = #goal_tac d}
fun update_lemma_tac f (Data d) = Data{lemma = #lemma d, lemma_tac = f (#lemma_tac d), goal_tac = #goal_tac d}
fun update_goal_tac f (Data d) = Data{lemma = #lemma d, lemma_tac = #lemma_tac d, goal_tac = f (#goal_tac d)}

fun set_lemma lemma = update_lemma (K lemma)
fun set_lemma_tac tac = update_lemma_tac (K tac)
fun set_goal_tac tac = update_goal_tac (K tac)

val empty = Data{lemma = NONE, lemma_tac= "", goal_tac= ""};

structure LemmaData = Proof_Data (type T = T
                                fun init _ = empty)
(* Getting and setting LemmaData of a context *)
val lemma_of_ctxt = get_lemma o LemmaData.get
val lemma_tac_of_ctxt = get_lemma_tac o LemmaData.get
val goal_tac_of_ctxt = get_goal_tac o LemmaData.get

fun set_lemma_ctxt lemma ctxt =
  LemmaData.put (set_lemma lemma (LemmaData.get ctxt)) ctxt
fun set_lemma_tac_ctxt tac ctxt =
  LemmaData.put (set_lemma_tac tac (LemmaData.get ctxt)) ctxt
fun set_goal_tac_ctxt tac ctxt =
  LemmaData.put (set_goal_tac tac (LemmaData.get ctxt)) ctxt

fun reset_lemma_data_ctxt ctxt = LemmaData.put empty ctxt;

(* FIXME: Use Pretty to make sure indentations are done properly instead of spaces... *)
 fun mk_proof_str_w_lemma ctxt  = 
   let
    val lemma = the (lemma_of_ctxt ctxt);
    val vars_n_types = Hipster_Utils.frees_of (Thm.prop_of lemma)
    val lemma_str = Library.quote (Syntax.string_of_term ctxt (Thm.prop_of lemma))
    val vars_str = String.concatWith " " (map fst vars_n_types);
    val tactic_str = lemma_tac_of_ctxt ctxt 
    val other_tac_str = goal_tac_of_ctxt ctxt   
  in
    "proof- \n  have " ^ lemma_str ^ " for " ^ vars_str ^ 
    "\n    by " ^ tactic_str  ^"\n" ^ "  then show ?thesis by " ^ other_tac_str ^"\nqed"
  end

end

