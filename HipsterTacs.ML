(* Various tactics for Hipster. Induction, simplification and metis. *)

signature HIPSTER_TACS =
sig 
  type hardtac
  val prove_by_simp : Proof.context -> tactic
  val timed_metis_tac : Proof.context -> Thm.thm list -> int -> tactic
  val simp_or_metis : Proof.context -> thm list -> tactic 
  val induct_simp_metis : Proof.context -> Thm.thm list -> tactic
  val induct_and_simp : hardtac
  val try_inductable_vars : Proof.context -> thm list -> hardtac -> int -> tactic
  val induct_simp_or_metis : hardtac
  val induct_simp_tac : Proof.context -> thm list -> tactic
end

structure Hipster_Tacs : HIPSTER_TACS =
struct

type hardtac = Proof.context -> thm list -> thm list option -> string -> int -> tactic

(*-----------------------------------------------------------------------------------------*)
(* Simp tactics *) 
(*-----------------------------------------------------------------------------------------*)


(* Apply simp to all subgoals *)
fun simp_all ctxt = ALLGOALS (Simplifier.asm_full_simp_tac ctxt);
 
(* Fails if all there are some subgoals left after application of simp *)
fun prove_by_simp ctxt = SOLVE (simp_all ctxt);


(*-----------------------------------------------------------------------------------------*)
(* Metis tactics *) 
(*-----------------------------------------------------------------------------------------*)

fun SOLVE_TIMEOUT mseconds tac t = 
    let
      val res = TimeLimit.timeLimit (Time.fromMilliseconds mseconds)
                 (fn () => SINGLE (SOLVE tac) t) ()
                 handle TimeLimit.TimeOut => NONE
                      | ERROR _ => NONE
    in
      case res of
        NONE => Seq.empty
      | SOME t' => Seq.single t'
    end;

(* Apply simp, if that doesn't work try metis.  *)
fun timed_metis_tac ctxt facts i =
    SOLVE_TIMEOUT 500
    (Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.metis_default_lam_trans ctxt facts i);

(* First simp, and if nessecary, let Metis deal with the rest *)
fun simp_or_metis ctxt facts = 
    SOLVE((ALLGOALS ((Simplifier.asm_full_simp_tac ctxt))
            THEN
            IF_UNSOLVED 
            (ALLGOALS (timed_metis_tac ctxt facts))));


(*-----------------------------------------------------------------------------------------*)
(* Figure out what we can do induction on, and tries each variable until sucess.*) 
(* Stolen from IsaPlanner...                                                               *)
(*-----------------------------------------------------------------------------------------*)

(* find an element, but keep the rest also *)
fun pull_elem f l = 
    let fun recf [] _ = NONE
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
            (case pull_elem (fn (n,_) => n = h) ithings of 
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
                     ((Hipster_Utils.frees_of t) @ 
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



(*-----------------------------------------------------------------------------------------*)
(* Induction tactics.                                                                      *)
(*-----------------------------------------------------------------------------------------*)

(* Apply induction on var and try to prove all cases by simp *)
fun induct_and_simp ctxt facts rule var i = 
     (induct_on_var_tac rule var i) THEN (prove_by_simp ctxt);

(* Induction on var, then try to prove resulting subgoals by simp or metis *)
fun induct_simp_or_metis ctxt facts rule var i = 
    (induct_on_var_tac rule var i) THEN (simp_or_metis ctxt facts);

(* Try induction on each variable in vars until we find one that allows a proof. *)
fun try_induct_on ctxt facts rule strat vars i  =
    case vars 
       of [] => no_tac 
        | (v :: vs) =>  
          (*(induct_simp_or_metis ctxt facts rule v i)*)
          strat ctxt facts rule v i
          ORELSE 
          (try_induct_on ctxt facts rule strat vs i);

(* Find the variables we can induct on *)
fun try_inductable_vars ctxt facts strat i thm = 
    let
      val vars = map fst (fst (inductable_things_in_sg i thm))
    in
      (try_induct_on ctxt facts NONE strat vars i) thm
    end;


(* An induction tactic to paste into the proof-script afterwards *)
fun induct_simp_metis ctxt lemmas thm = 
    let
      val ctxt' = Library.foldl (fn (ctxt,thm) => Simplifier.add_simp thm ctxt)
                                (ctxt, lemmas)
    in
      ALLGOALS(try_inductable_vars ctxt' lemmas induct_simp_or_metis) thm
    end

(* An induction tactic to paste into the proof-script afterwards *)
fun induct_simp_tac ctxt lemmas thm = 
    let
      val ctxt' = Library.foldl (fn (ctxt,thm) => Simplifier.add_simp thm ctxt)
                                (ctxt, lemmas)
    in
      ALLGOALS(try_inductable_vars ctxt' lemmas induct_and_simp) thm
    end


end


