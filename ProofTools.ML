(*------------------------------------------------------------------------------------*)
(* Proof tools and tactics for induction and simplification, porting HipSpec's proof-
   loop into the Isabelle setting. *)
(*------------------------------------------------------------------------------------*)

(* TODO:  Try to use some suitable heuristic to get things in nice order! *)

structure ProofTools =
struct

(*------------------------------------------------------------------------------------*)
(* Term mainipulation stuff, stolen from IsaPlanner... *)
(*------------------------------------------------------------------------------------*)

fun add_term_frees (t, frees: Term.term list) = 
    case t of
      Free   _ => Ord_List.insert Term_Ord.term_ord t frees
      | Abs (_,_,body) => add_term_frees(body,frees)
      | f$t =>  add_term_frees (f, add_term_frees(t, frees))
      | _ => frees;

fun add_typ_tfrees (Type(_,Ts),fs) = List.foldr add_typ_tfrees fs Ts
      | add_typ_tfrees(TFree(f),fs) = insert (op =) f fs
      | add_typ_tfrees(TVar(_),fs) = fs;

fun frees_of t = map Term.dest_Free (add_term_frees (t,[]));
fun typ_tfrees_of ty = add_typ_tfrees(ty,[]);

(* Get a pair of (type-frees, term frees) without dups. *)
fun frees_and_tfrees_of_thm thm = 
    let 
      val t = Thm.concl_of thm
    in (map fst (typ_tfrees_of (Term.fastype_of t)), map fst (frees_of t)) end;

(*------------------------------------------------------------------------------------*)
(* Figure out what we can do induction on. Stolen from IsaPlanner... *)
(*------------------------------------------------------------------------------------*)

(* find an element, but keep the rest also *)
fun pull_elem f l = 
    let fun recf [] L = NONE
          | recf (h :: t) L = 
            if f h then SOME (h, (rev L) @ t)
            else recf t (h :: L)
    in recf l [] end;

(* re-arranges things to induct on (indnames) into the correct format
for Isabelles induction tactic, also removed them from ithings, so
that we know what other frees to turn into sinks (univ quantifies in
the IH) *)
(* assumes: indnames <= ithings *)
fun mk_induct_insts ithings indnames = 
    let 
      fun faux ithings [] L = (ithings, rev L)
        | faux ithings (h :: t) L = 
          if h = "_" then (faux ithings t (NONE :: L))
          else 
            (case pull_elem (fn (n,ty) => n = h) ithings of 
               NONE => 
               raise ERROR ("No such variable to do induction on: " ^ h)
             | SOME (v, ithings') => (faux ithings' t ((SOME v) :: L)));
    in faux ithings indnames [] end;


(* the free variables of a term that are of a datatype 
   (can have induction applied) *)
fun inductable_things_in_term thry t = 
    let 
      fun lookup thy s =
          case (Datatype.get_info thy s) of
             NONE => NONE
           | SOME di => SOME (#induct di);

      fun datatype_chk (Type(tn,_))  = 
           Basics.is_some (lookup thry tn)
        | datatype_chk _ = false;
    in 
      (* Return frees and forall quantified vars (if any) *)
      (* Split into those we can do structural induction over, and the rest *)
       List.partition (datatype_chk o snd) 
                     ((frees_of t) @ 
                     (Term.strip_all_vars t))
    end;

fun inductable_things_in_sg i th = 
    inductable_things_in_term 
      (Thm.theory_of_thm th) 
      (Library.nth (prems_of th) (i - 1));

(* Rule can be NONE if we just want plain structural induction. *)
(* var is the variable we want to do induction on *)
fun induct_on_var_tac rule var i goalthm = 
    let
        (*Dummy context for the sake of Isar*)
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm goalthm);
      val (ithings, non_ithings) = inductable_things_in_sg i goalthm;
      val (otherfrees, inductfrees) = mk_induct_insts ithings [var];
      val insts = [map (fn NONE => NONE | SOME v => 
                                          (* FIXME: Each variable paired with false? *)
                                          SOME (NONE : Binding.binding option,(Free v,true)))
                         inductfrees];
         (* Throw away Isar related stuff and only take the Thm.thm seq *)
      val nw_thms = 
          Seq.map snd (Induct.induct_tac
                         ctxt false insts [non_ithings @ otherfrees] [] rule [] i goalthm)
      in
        nw_thms
      end;


(*------------------------------------------------------------------------------------*)
(* Isabelle tactic for proving things from HipSpec *)
(*------------------------------------------------------------------------------------*)



datatype ConjQueue = ConjQ of {open_conjs : Thm.thm list, (* left to prove *)
                               failed : Thm.thm list,     (* Have tried once but failed *)
                               proved : Thm.thm list,     (* proved *)
                               simps : simpset, (* the HOL simpset + stuff we have proved *) 
                               ctxt : Proof.context,
                               progress : bool};          (* have we proved at least something this iteration *)

(* Apply simp to all subgoals *)
fun simp_all simpset = ALLGOALS (Simplifier.asm_full_simp_tac simpset);
 
(* Fails if all there are some subgoals left after application of simp *)
fun prove_by_simp simpset conj = SOLVE (simp_all simpset) conj;

(* Apply induction and try to prove all cases by simp *)
fun induct_and_simp simpset rule var i = 
     (induct_on_var_tac rule var i) THEN (prove_by_simp simpset);

(* Try induction on each variable until we find one that works *)
fun try_induct_on simpset rule vars i  =
    case vars 
       of [] => no_tac 
        | (v :: vs) =>  
          (induct_and_simp simpset rule v i)
          ORELSE 
          (try_induct_on simpset rule vs i);
fun induct_on_goal simpset i thm = 
    let
      val vars = map fst (fst (inductable_things_in_sg i thm))
    in
      try_induct_on simpset NONE vars i thm
    end;


(* Assmume get list of strings from HipSpec, which can be directly parsed as Isabelle terms*)
fun mk_conjs ctxt lemma_strs = 
    let
      val thy = Proof_Context.theory_of ctxt
      val conjs = map (Goal.init o (Thm.cterm_of thy) o (Syntax.read_prop ctxt)) lemma_strs;
      (* val conjs = map (Syntax.read_prop ctxt) lemma_strs; *)
    in
      (* NOTE: Isabelle2013-2 use contexts instead of simpsets. Nicer, if we also can get things
       to work with bloody JEdit. *)
      ConjQ{open_conjs = conjs, failed = [], proved = [], ctxt = ctxt, 
            simps = Simplifier.simpset_of ctxt, progress = false}
    end;

fun try_nxt_conj ctxt (ConjQ q) =
    case (#open_conjs q) of
      (*retry open_conjs if we have some new proved since last time.*)
      [] => if (#progress q) 
            then SOME (ConjQ{open_conjs = (#failed q),
                       failed = [],
                       proved = #proved q,
                       ctxt = #ctxt q,
                       simps = #simps q,
                       progress = false}) 
            else NONE

    | (c::cs) => (* try proving next open conj *) 
      let 
        val r = prove_by_simp (#simps q) c
      in
      case (Seq.pull r) of (* Discard this, it is trivial *)
        SOME _ => 
        let val _ = writeln "discarded something"
        in
        SOME 
          (ConjQ{open_conjs = cs,
                 failed = #failed q,
                 proved = #proved q,
                 ctxt =  #ctxt q,
                 simps = #simps q,
                 progress = #progress q})
        end
      | NONE =>
        let
          val res = (ALLGOALS (induct_on_goal (#simps q))) c;
        in
          (* Only care about first proof found *)
          (case Seq.pull res of 
             SOME (proved_thm, _) => 
             let 
               (* Thm used by simp need to be lifted so it use meta-variables *)
               val final_thm = Goal.finish ctxt proved_thm
               val simp_thm = Drule.generalize (frees_and_tfrees_of_thm final_thm) final_thm
             in
               SOME (ConjQ{open_conjs = cs,
                         failed = (#failed q),
                         proved = final_thm::(#proved q),
                         ctxt =  #ctxt q,
                         simps = Simplifier.add_simp simp_thm (#simps q),
                         progress = true})
             end
           (* NONE indicates that the tactic failed to prove c *)
           | NONE => SOME (ConjQ{open_conjs = cs,
                                 failed = c::(#failed q),
                                 proved = (#proved q),
                                 ctxt =  #ctxt q,
                                 simps = #simps q,
                                 progress = #progress q})
          )
        end
      end;

(* Run the hipspec-loop: try proving conjectures until done or no more progress can be made" *)
fun hipspec_loop ctxt lemmas =
    let 
      val conjs =  mk_conjs ctxt (Library.split_lines (Library.trim_line lemmas))

      fun recf (ConjQ q) = 
          case (try_nxt_conj ctxt (ConjQ q)) of
            NONE => (rev (#proved q), (#simps q), rev (#failed q))
          | SOME q' => recf q'
    in
      recf conjs
    end;

end; (* struct *)
