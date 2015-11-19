
signature INDUCT_CTAC =
sig

type hardCTac = Thm.thm list option -> string list option -> CTac.ctactic

val try_inductable_vars_ctac : hardCTac -> int -> CTac.ctactic

end

structure Induct_CTac  : INDUCT_CTAC = 
struct

type hardCTac =  Thm.thm list option -> string list option -> CTac.ctactic

(* TODO: Implement and record if simp or metis+which facts should be used to replay *)
val simp_or_sledgehammer_ctac = CTac.all_ctac;

(* TODO : Implement context data to record induction on variable var *)
fun induct_on_var_ctac rule var (ctxt,thm) = 
  let 
    val results = (CTac.AS_CTACTIC (HEADGOAL (Ind_Tacs.induct_on_var_tac ctxt rule var))) (ctxt,thm)
  in 
    Seq.map (fn (ctxt',thm') => (Proof_Data.set_ind_var ctxt var, thm')) results
  end;

(* Induction on a var, then try to prove by sledgehammer *)
fun induct_and_sledgehammer_ctac rule var =
    CTac.CTHEN 
        (CTac.DEPTH_SOLVE
          ((Seq.DETERM (induct_on_var_ctac rule var))), 
        simp_or_sledgehammer_ctac)

 
(* Try induction (using the strategy strat) 
   on each variable in vars, until we find one that allows a proof. 
   rule states if we are to use some particular induction rule, e.g.
   recursion induction. If rule is NONE, we do stuctural induction. *)
fun try_induct_on rule strat vars i =
  case vars of
    []        => CTac.no_ctac 
  | (v :: vs) => 
    CTac.CORELSE
      (strat rule (SOME v),
      try_induct_on rule strat vs i) 

(* Structural Induction: Find the variables we can induct on *)
fun try_inductable_vars_ctac strat i (ctxt,thm) = 
    let 
      val vars = map (fn (v,_) => [v]) (fst (Ind_Tacs.inductable_things_in_sg ctxt i thm))
    in 
      (try_induct_on NONE strat vars i) (ctxt,thm)
    end;

end