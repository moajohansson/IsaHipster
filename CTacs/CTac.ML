(*  Author:     Moa Johansson, Chalmers University of Technology *)

(* Contextual tactics: Tactics that carry a context to record what they do.
   useful for tactics that do search, e.g. induction, then we can record
   what induction scheme, variable and lemmas were needed.
*)


signature CONTEXTUAL_TACTIC =
sig
type ctactic = (Proof.context * Thm.thm) -> (Proof.context * Thm.thm) Seq.seq

val AS_CTACTIC : tactic -> ctactic;
val AS_TAC : Proof.context -> ctactic -> tactic;

val all_ctac : ctactic;
val no_ctac : ctactic;

val CTHEN : ctactic * ctactic -> ctactic;
val CORELSE : ctactic * ctactic -> ctactic; 
val CTHEN': ('a -> ctactic) * ('a -> ctactic) -> 'a -> ctactic
val CORELSE': ('a -> ctactic) * ('a -> ctactic) -> 'a -> ctactic

val CHANGED_PROP : ctactic -> ctactic;
val COND: (Proof.context * Thm.thm -> bool) -> ctactic -> ctactic -> ctactic

val CTHEN_MAYBE: ctactic * ctactic -> ctactic
val CTHEN_MAYBE': ('a -> ctactic) * ('a -> ctactic) -> 'a -> ctactic

val TRY: ctactic -> ctactic
val TRY': ('a -> ctactic) -> 'a -> ctactic
val CHANGED :  ctactic -> ctactic
val SOLVE_OR_FAIL : ctactic -> ctactic 

val ALLGOALS: (int -> ctactic) -> ctactic;
val HEADGOAL: (int -> ctactic) -> ctactic;
val SINGLE: ctactic -> (Proof.context * Thm.thm) -> (Proof.context * Thm.thm) option

val DEPTH_FIRST: ((Proof.context * Thm.thm) -> bool) -> ctactic -> ctactic
val DEPTH_SOLVE: ctactic -> ctactic
val IF_UNSOLVED: ctactic -> ctactic
val SOLVE_TIMEOUT : int -> ctactic -> ctactic

end 


structure CTac : CONTEXTUAL_TACTIC  = 
struct

infix 1 CTHEN CTHEN'
infix 0 CORELSE CORELSE'
infix 1 CTHEN_MAYBE CTHEN_MAYBE';

type ctactic = (Proof.context * Thm.thm) -> (Proof.context * Thm.thm) Seq.seq

(* ------------------------------------------------------------------------------------------ *)
(* Tacticals, for combining ctactics *)
(* ------------------------------------------------------------------------------------------ *)


(* Creates a dummy ctactic from a regular tactic, that doesn't record any info in its context *)
fun AS_CTACTIC tac = fn (ctxt,thm) => (Seq.map (fn nwthm => (ctxt,nwthm)) (tac thm));

(* Treat a ctactic as a regular tactic, which trows away the context part. *)
fun AS_TAC ctxt ctac = fn thm => (Seq.map snd (ctac (ctxt,thm)));

(* ------------------------------------------------------------------------------------------ *)

(*passes all proofs through unchanged;  identity of THEN*)
fun all_ctac st = Seq.single st;

fun no_ctac _ = Seq.empty;

(*the tactical THEN performs one tactic followed by another *)
fun (ctac1 CTHEN ctac2) st = Seq.maps ctac2 (ctac1 st);

fun (ctac1 CTHEN' ctac2) x = ctac1 x CTHEN ctac2 x;

(*The tactical ORELSE uses the first tactic that returns a nonempty sequence.
  Like in LCF, ORELSE commits to either tac1 or tac2 immediately.
  Does not backtrack to tac2 if tac1 was initially chosen. *)
fun (ctac1 CORELSE ctac2) st =
    case Seq.pull(ctac1 st) of
        NONE       => ctac2 st
      | sequencecell => Seq.make(fn()=> sequencecell);

fun (ctac1 CORELSE' ctac2) x = ctac1 x CORELSE ctac2 x;


(*Conditional tactical: testfun controls which tactic to use next.
  Beware: due to eager evaluation, both thentac and elsetac are evaluated.*)
fun COND testfun thenf elsef = (fn prf =>
    if testfun prf then thenf prf else elsef prf);

(*Do the tactic or else do nothing*)
fun TRY ctac = ctac CORELSE all_ctac;
fun TRY' ctac1 x = TRY (ctac1 x);

(*Execute tac1, but only execute tac2 if there are at least as many subgoals
  as before.  This ensures that tac2 is only applied to an outcome of tac1.*)
fun (ctac1 CTHEN_MAYBE ctac2) (ctxt,thm) =
  (ctac1 CTHEN COND (has_fewer_prems (Thm.nprems_of thm) o snd) all_ctac ctac2) (ctxt,thm);

fun (ctac1 CTHEN_MAYBE' ctac2) x = ctac1 x CTHEN_MAYBE ctac2 x;

(* ------------------------------------------------------------------------------------------ *)
(*Accept only next states that change the theorem somehow*)
fun CHANGED ctac (ctxt,thm) =
  let fun diff (_,thm') = not (Thm.eq_thm (thm, thm'));
  in Seq.filter diff (ctac (ctxt,thm)) end;

(*Accept only next states that change the theorem's prop field
  (changes to signature, hyps, etc. don't count)*)
fun CHANGED_PROP ctac st =
  let fun diff st' = not (Thm.eq_thm_prop (snd st, snd st'));
  in Seq.filter diff (ctac st) end;

fun SINGLE ctacf = Option.map fst o Seq.pull o ctacf

(*Apply a tactic if subgoals remain, else do nothing.*)
val IF_UNSOLVED = COND ((has_fewer_prems 1) o snd) all_ctac;

fun SOLVE_OR_FAIL ctac st =  
  let fun solved st = has_fewer_prems 1 (snd st);
  in Seq.filter solved (ctac st) end;
(* ------------------------------------------------------------------------------------------ *)

(*For n subgoals, performs tac(n) THEN ... THEN tac(1)
  Essential to work backwards since tac(i) may add/delete subgoals at i. *)
fun ALLGOALS ctac st =
  let fun doall 0 = all_ctac
        | doall n = ctac(n) CTHEN doall(n-1)
  in  doall (Thm.nprems_of (snd st)) st  end;

(*First subgoal only.*)
fun HEADGOAL ctac = ctac 1;

(* ------------------------------------------------------------------------------------------ *)
(*Searches until "satp" reports proof tree as satisfied.
  Suppresses duplicate solutions to minimize search space.*)
fun DEPTH_FIRST satp ctac =
 let 
     fun equal_thm ((_,t1),(_,t2)) = Thm.eq_thm (t1,t2)
     fun depth _ [] = NONE
       | depth used (q::qs) =
          case Seq.pull q of
              NONE         => depth used qs
            | SOME(st, stq) =>
                if satp st  andalso not (member equal_thm used st)
                then SOME(st, Seq.make
                                 (fn()=> depth (st::used) (stq::qs)))
                else depth used (ctac st :: stq :: qs)
  in (fn st => 
      case (depth [] [Seq.single st]) of
        NONE => Seq.empty
      | SOME(st2,_) => Seq.single st2)      
 end;

val DEPTH_SOLVE = DEPTH_FIRST ((has_fewer_prems 1) o snd);

(* ------------------------------------------------------------------------------------------ *)

fun SOLVE_TIMEOUT mseconds ctac st = 
  let val res = TimeLimit.timeLimit (Time.fromMilliseconds mseconds)
                  (fn () => SINGLE ctac st) ()
                handle TimeLimit.TimeOut => NONE
                     | ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  in
    case res of
      NONE => Seq.empty 
    | SOME st' => Seq.single st'
  end;

(* ------------------------------------------------------------------------------------------ *)
(* Some basic tactics as ctactics                                                             *)
(* ------------------------------------------------------------------------------------------ *)


end; 
