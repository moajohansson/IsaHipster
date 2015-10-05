(* Various tactics for Hipster. Induction, simplification and metis. *)

(* TODO: checkout Type.could_unify
          --> and: purely structural matching (raw_match, etc)
         else Term.could_unify (for terms...) *)

signature IND_TACS =
sig 
  type hardtac
  val simp_all : Proof.context -> thm list -> tactic
  val prove_by_simp : Proof.context -> thm list -> tactic
  val timed_metis_tac : Proof.context -> bool -> Thm.thm list -> int -> tactic
  val simp_or_metis : Proof.context -> (thm list * thm list) -> tactic 

  val induct_and_simp : thm list -> hardtac
  val induct_simp_or_metis : thm list * thm list -> hardtac

  val try_inductable_vars : Proof.context -> hardtac -> int -> tactic
  val induct_for_me : Proof.context -> string list list -> string -> int -> tactic

  (* Context -> tactic, to be pasted into proof script. *)
  val induct_simp_tac : Proof.context -> tactic

  (* Context -> list of simp rules (defs) -> tactic, to be pasted into proof script. *)
  val induct_simp_metis : Proof.context -> thm list -> tactic
  
  (* Context -> list of induct rules (schemes) -> tactic *)
  val induct_with_schemes : Proof.context -> thm list -> tactic
  val try_induct_schemes : Proof.context -> hardtac -> int -> tactic
  (*val try_induction_with : Proof.context -> thm list list -> hardtac -> vars -> int -> tactic*)

end

structure Ind_Tacs  : IND_TACS  =
struct

type hardtac = Proof.context -> thm list option -> string list option -> int -> tactic
(* XXX: string option seems better than checking for nulls string, right? *)

fun SOLVE_TIMEOUT mseconds tac t = 
    let
      val res = TimeLimit.timeLimit (Time.fromMilliseconds mseconds)
                 (fn () => SINGLE ( tac) t) ()
                 handle TimeLimit.TimeOut => NONE
                      | ERROR _ => NONE
    in
      case res of
        NONE => Seq.empty (*let val _ = Pretty.writeln (Pretty.str "Timeout :(") in Seq.empty end*)
      | SOME t' => Seq.single t'
    end;

(*-----------------------------------------------------------------------------------------*)
(* Simp tactics *) 
(*-----------------------------------------------------------------------------------------*)
(*fun pretty_thm ctxt thm = Syntax.pretty_term ctxt (prop_of thm);*)


(* Apply simp to all subgoals *)
fun simp_all ctxt lemmas thm = 
    let
       (*val _ = Pretty.writeln (Pretty.block [Pretty.str "simp_all: ", pretty_thm ctxt thm])*)
       (*val _ = @{print} thm  OR @{make_string} *)
       (*val ss = map @{print} lemmas*)
       val ctxt' = Library.foldl (fn (ctxt,thm) => Simplifier.add_simp thm ctxt)
                                 (ctxt, lemmas)
    in
      (PARALLEL_GOALS o ALLGOALS) (fn i => SOLVE_TIMEOUT 500 (Simplifier.asm_full_simp_tac ctxt' i)) thm
    end;

(* Fails if all there are some subgoals left after application of simp *)
 fun prove_by_simp ctxt lemmas = SOLVE_TIMEOUT 500 (simp_all ctxt lemmas); 


(*-----------------------------------------------------------------------------------------*)
(* Metis tactics *) 
(*-----------------------------------------------------------------------------------------*)


(* Apply simp, if that doesn't work try metis.  *)
  (*  val _ = Pretty.writeln (Pretty.block [Pretty.str ("timed_metis: "^ @{make_string} i),pretty_thm ctxt thm]) in*)
fun timed_metis_tac ctxt full facts i thm = 
  let val timeout = Hip_Tac_Ops.metis_to ctxt
      val args_metis = (if full then [ATP_Proof_Reconstruct.full_type_enc] else [])
  in (SOLVE_TIMEOUT timeout
       (Metis_Tactic.metis_tac args_metis
        ATP_Proof_Reconstruct.default_metis_lam_trans ctxt facts i)) thm
 end;

val has_tvar = exists_type (exists_subtype (fn TVar _ => true | _ => false)) o Thm.prop_of

fun metis_method ((override_type_encs, lam_trans), ths) ctxt facts =
  let val (schem_facts, nonschem_facts) = List.partition has_tvar facts
      val timeout = Hip_Tac_Ops.metis_to ctxt
  in
     (Method.insert_tac nonschem_facts THEN'
      CHANGED_PROP o (SOLVE_TIMEOUT timeout) o Metis_Tactic.metis_tac (these override_type_encs)
        (the_default ATP_Proof_Reconstruct.default_metis_lam_trans lam_trans) ctxt (schem_facts @ ths)) end

(*fun ALLsub tac st =
  let val subgoals = nprems_of st
      fun doall n max = if n < max then (tac(n) THEN_ELSE (doall n (max-1) ,doall(n+1) max)) else tac(n);
  in  doall 1 subgoals st  end;

fun ALLt tac st =
  let fun doall i max th =
        let val subgoals = nprems_of th
            val n = if subgoals < max then i else (i + 1)
        in (if n > subgoals then all_tac else (tac(n) THEN doall n subgoals)) th end; (*(if nprems_of th < max then tac(n) THEN doall n (nprems_of th)
                                                        else tac(n+(max-(nprems_of th))) THEN doall n (nprems_of th)) th)*)
        (*| doall n = tac(n) THEN_ELSE (doall(n-1),doall(n-1))*)
  in  doall 0 (nprems_of st) st  end;

fun xxx  ctxt facts tac =( ALLGOALS (Method.insert_tac facts) THEN
        (CHANGED_PROP o PARALLEL_GOALS o ALLGOALS o tac) ctxt)*)

(* First simp, and if nessecary, let Metis deal with the rest *)
fun simp_or_metis ctxt (facts, lemmas) thm = (*let val _ = Pretty.writeln (pretty_thm ctxt thm) in*)
  let
    val type_enc = if Hip_Tac_Ops.use_full_types ctxt then (SOME [ATP_Proof_Reconstruct.full_type_enc]) else NONE
    val simp_adds = filter (fn lem => hd (Hip_Tac_Ops.simp_cond ctxt) (thm,lem)) lemmas
    val metis_adds = filter (fn lem => hd (Hip_Tac_Ops.metis_cond ctxt) (thm,lem)) (lemmas)
  in
    ((simp_all ctxt simp_adds) (* FIXME: both facts and lemmas? *)     (*SOLVE_TIMEOUT 2000*) 
     THEN
     IF_UNSOLVED
     ((PARALLEL_GOALS o ALLGOALS) (metis_method ((type_enc,NONE), metis_adds) ctxt facts))) thm
  end;
(*REPEAT o FIRSTGOAL*) (*REPEAT_FIRST*)
(*((REPEAT_ALL_NEW (metis_method ((NONE,NONE), lemmas) ctxt facts))))*)
(*-----------------------------------------------------------------------------------------*)
(* Figure out what we can do induction on, and tries each variable until success.*) 
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
          if h = "_"
            then (faux ithings t (NONE :: L))
            else (case pull_elem (fn (n,_) => n = h) ithings of 
                    NONE => raise ERROR ("No such variable to do induction on: " ^ h)
                  | SOME (v, ithings') => (faux ithings' t ((SOME v) :: L)));
    in faux ithings indnames [] end;

(*   val find_inductT: Proof.context -> typ -> thm list *)
(* let              
              val ctxt = Proof_Context.init_global thry;
              val _ = Pretty.writeln (pretty_thm ctxt (#induct di)) ;
              val _ = Pretty.writeln (Pretty.block (map (pretty_thm ctxt) (#inducts di))) ;
             in *)
(*  let
            val ctxt = Proof_Context.init_global thry;
            val indds = Induct.find_inductT ctxt (Type(tn,xxx)) ;
            (*val _ = Pretty.writeln (Pretty.block (map (pretty_thm ctxt) indds)) ;*)
           in*)


(* the free variables of a term that are of a datatype 
   (can have induction applied) *)
fun inductable_things_in_term ctxt t =
    let 
      fun lookup s =
        case (BNF_FP_Def_Sugar.fp_sugar_of ctxt s) of
          NONE => NONE
        | SOME di => SOME (di |> #fp_co_induct_sugar |> #co_inducts |> hd);
      fun datatype_chk (Type(tn,_)) =
            Basics.is_some (lookup tn)
        | datatype_chk _ = let val _ = @{print}"not a type!!" in false end;
    in
      (* Return frees and forall quantified vars (if any) *)
      (* Split into those we can do structural induction over, and the rest *)
       List.partition (datatype_chk o snd)
                      ((Hipster_Utils.frees_of t) @
                       (Term.strip_all_vars t))
    end;

fun inductable_things_in_sg ctxt i thm =
    inductable_things_in_term
      ctxt
      (Library.nth (Thm.prems_of thm) (i - 1)) (* XXX: check how this might affect us *)

fun infer_term x ctxt =
     let val (T, ctxt') = Proof_Context.inferred_param x ctxt
     in (Free (x, T), ctxt') end;

fun induct_for_me ctxt xss rule i =
     let
       val (tss, ctxt') = (fold_map o fold_map) infer_term xss ctxt
       val instss = map (map (fn inst => SOME (NONE, (inst, false)))) tss;
       val ruleT = SOME (Sledgehammer_Util.thms_of_name ctxt' rule)
                        handle _ => NONE
     in Seq.map snd o Induct.induct_tac ctxt' false instss [] [] ruleT [] i end

(* Term: has_abs, dest_abs??
         typ_subst_atomic? *)
(*fun isHO *)


(* Rule can be NONE if we just want plain structural induction. *)
(* var is the variable we want to do induction on *)
fun induct_on_var_tac ctxt rule var i goalthm = 
    let
      val (ithings, non_ithings) = inductable_things_in_sg ctxt i goalthm;

      val (otherfrees, inductfrees) = (case var of
                                        NONE => mk_induct_insts ithings []
                                      | SOME v => mk_induct_insts ithings v (*[v]*))
      (*val (tss, ctxt') = (fold_map o fold_map) infer_term [case var of NONE => [] | SOME v=> [v]] ctxt
      val instss = map (map (fn inst => SOME (NONE, (inst, false)))) tss;*)
      (*val _ = @{print} inductfrees;
      val _ = @{print} rule;*)
      val insts = map (fn NONE => NONE | SOME v => 
                                          (* FIXME: Each variable paired with false?
                                           -- changed : testing : matters not in our case since we are wrapping them with 'Free' *)
                                          SOME (NONE : Binding.binding option,(Free v,false)))
                         inductfrees;
         (* Throw away Isar related stuff and only take the Thm.thm seq *)
      val _ = Pretty.writeln (Pretty.block ( [Pretty.str "induct_on: ", Pretty.str (Library.space_implode " * " (map (fn NONE => "; "
        | SOME (_, (Free (v,_),false)) => v) insts)), Pretty.str "; otherfrees: ", Pretty.str (Library.space_implode ", "
          (map (fn (v,_) => v) otherfrees)) ]));
      val nw_thms' = (Induction.induction_tac ctxt false [insts] [(*non_ithings*)otherfrees] [] rule [] i goalthm)
            handle ERROR _ => Seq.empty (* let val _ = Pretty.writeln (Pretty.str (" >> ERROR : " ^ t)) in Seq.empty end *)
      in
        (*Seq.cons (snd (Seq.hd nw_thms')) Seq.empty *)Seq.map snd nw_thms'

      end;


(*-----------------------------------------------------------------------------------------*)
(* Induction tactics.                                                                      *)
(*-----------------------------------------------------------------------------------------*)

(* Apply induction on var and try to prove all cases by simp *)
fun induct_and_simp lemmas ctxt rule var i = 
     DEPTH_SOLVE (
          (Seq.DETERM
            (HEADGOAL ((induct_on_var_tac ctxt rule var )))) THEN (prove_by_simp ctxt lemmas));

(* Induction on var, then try to prove resulting subgoals by simp or metis *)
fun induct_simp_or_metis (facts, lemmas) ctxt rule var i = 
    DEPTH_SOLVE (
          (Seq.DETERM
            (HEADGOAL ((induct_on_var_tac ctxt rule var)))) (*induct_on_var_tac ctxt rule var i*) THEN (simp_or_metis ctxt (facts,lemmas)));


(* Try induction on each variable in vars until we find one that allows a proof. *)
fun try_induct_on ctxt rule strat vars i =
    case vars
       of [] => (*strat ctxt NONE (* for now, no: rule - don't think it should ever work *) NONE i
                ORELSE*) no_tac
        | (v :: vs) =>  (*let val _ = Pretty.writeln (Pretty.str (" - vars: "^ @{make_string} v)) in*)
          (*(induct_simp_or_metis ctxt facts rule v i)*)
          strat ctxt rule (SOME v) i (*THEN simp_all ctxt []*)
          ORELSE
          (try_induct_on ctxt rule strat vs i)

(* Find the variables we can induct on *)
fun try_inductable_vars ctxt strat i thm = 
    let
      val vars = map (fn (v,_) => [v]) (*fst*) (fst (inductable_things_in_sg ctxt i thm))
      val _ = @{print} "argu"
      val _ = @{print} vars
    in
      (try_induct_on ctxt NONE strat vars i) thm
    end;

(*
  @{thm "drop.induct"};
  (Thm.concl_of @{thm "drop.induct"});
  (HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"}));
  @{term "case x of 0 \<Rightarrow> 0 | Suc y \<Rightarrow> y"};
  @{term "P y x"};
  val ump = binder_types (reP(HOLogic.dest_Trueprop (Thm.concl_of @{thm "drop.induct"})));
  val tumf = fastype_of @{term "Cons Z Nil"};
  hd (tl ump) = tumf;
  fastype_of1 ([],@{term "Cons Z Nil"});
  Type.could_match(hd (tl ump), tumf);*)

              (*val _ = @{print} vars
              val ruleVars = map fst (filter (fn v => exists (fn tr => Type.could_match (tr,snd v)) argTyps) vars)
              fun filter_matching t vs = filter (fn v => Type.could_match (t, snd v)) vs
              val rulSss = map (fn t => filter_matching t vars) argTyps
              val ruleSets = map (fn rv => filter (fn av => Type.could_match (rv, snd av)) vars) argTyps
              val _ = @{print} (ruleSets)
              val _ = @{print} rulSss
              fun paired [] = []
                | paired (v::vs) = map (fn w => [v,w]) vs @ paired vs
              val indvars = map (fn v => [v]) ruleVars @ paired ruleVars
              fun nonreptup [] = []
                | nonreptup (vs:: vss) = fold (fn v => fn acc => acc @ (map (fn ts => v::ts) (nonreptup (map (filter (fn t => not (v = t))) vss)))) vs [] @ nonreptup vss
              val _ = @{print} nonreptup ruleSets*)

  fun reP uu = case uu of
        Var (_,t) => t
      | (t$_) => reP t
      | (Abs (_, t, _)) => t
      | (Free (_, t)) => t; (* TODO: Bound, Const *)

fun try_induction_with ctxt scheme_rules strat vars i =
    (* let val vars = map fst (fst (inductable_things_in_sg i thm)) *)
    let val struct_tac =
          (*let val _ = Pretty.writeln (Pretty.str "Rule: none")
          in*) try_induct_on ctxt NONE strat (map (fn (v,_) => [v]) (*fst*) vars) i
        fun rec_ind_tac rules =
              case rules of
                []            => no_tac
              | ((n,r) :: rs) =>
                  let val _ = Pretty.writeln (Pretty.str ("Rule: "^n))
                      val argTyps = binder_types (reP (HOLogic.dest_Trueprop (Thm.concl_of ((hd o the) r))))
                      val all_instances = (Scheme_Instances.instances_for_with argTyps vars)
              (*val instances = Scheme_Instances.flatten_instances true all_instances(* (Scheme_Instances.instances_for_with argTyps vars)*)*)
                      val instt = hd all_instances
              (*val _ = @{print} instances   val _ = @{print} instt*)
              (* FIXME: vars types filter *)
                  in
                    try_induct_on ctxt r strat (map (map fst) instt) i
                    ORELSE
                    (rec_ind_tac rs) (*ctxt rs strat vars i*) end;
    in struct_tac ORELSE rec_ind_tac scheme_rules end;


fun try_induct_schemes ctxt strat i thm =
    let
      val vars = fst (inductable_things_in_sg ctxt i thm) (* map fst ... *)
      val _ = @{print} vars
      (*val lemmas = ThyExpl_Data.proved_of_ctxt ctxt @ Hipster_Rules.get ctxt*)
      val thynm = Context.theory_name (Proof_Context.theory_of ctxt)
      val consts = Hipster_Utils.thy_consts_of thynm thm
      val thinds = map (fn n => (n, SOME (Sledgehammer_Util.thms_of_name ctxt n))
                        handle _ => (n, NONE) ) ((*"Naturals.leq.induct" ::*)distinct (op =) (map (fn c => (c^".induct")) consts))
      val schemes = rev (*the o snd*) (filter (Basics.is_some o snd) thinds)
      (*val _ = Pretty.writeln (pretty_thm ctxt thm)*)
      (* FIXME: distinct ... *)
    in (try_induction_with ctxt schemes strat (distinct (op =) vars) i) thm
    end;

(* QUESTION: Should these tactics really add the lemma-list to the simplifier?
The tactics used by Hipster don't, they only pass them to Metis, looking them up from the ctxt. 
However, if these tactics are used outside of theory exploration, they might not have all the
stuff in the ctxt, i.e. simprules and discovered theorems? 

Maybe need all separate tactics for outside Theory Exploration? Or data for induction? 
Or add to TacticData?
*)

(* An induction tactic to paste into the proof-script afterwards *)
fun induct_simp_metis ctxt facts thm = 
    let
      val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
    in
      (* XXX: removed as simplifier rules - in this case, so far, no changes *)
      ALLGOALS(try_inductable_vars ctxt (induct_simp_or_metis (facts,lemmas))) thm
    end;

(* lookup @{theory} "conj" 
val lookup = Symtab.lookup o Data.get
fun update k v = Data.map (Symtab.update (k, v)) *)

fun induct_with_schemes ctxt facts thm =
    let
      val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
      (*val thynm = Context.theory_name (Proof_Context.theory_of ctxt)
      val consts = Hipster_Utils.thy_consts_of thynm thm*)
      (*val _ = Pretty.writeln (Pretty.block (Pretty.str "Theorem: " :: [pretty_thm ctxt thm]))
      val _ = Pretty.writeln (Pretty.str ("Num cs = " ^ @{make_string} (length consts)))
      val _ = Pretty.writeln (Pretty.str (Library.space_implode " " (thynm ^ "-Consts: " :: consts))) *)
      (*val thinds = map (fn n => (n, SOME (Sledgehammer_Util.thms_of_name ctxt n))
                        handle _ => (n, NONE) ) (map (fn c => (c^".induct")) consts)*)
      (*val thinds' = map (fn n => (n,  (Attrib.thms n))
                         handle _ => (n, NONE) ) (map (fn c => (c^".induct")) consts)*)
      (*val _ = Pretty.writeln (Pretty.block (maps (fn (n,thms) => (case thms of
           SOME ts => map Pretty.str ("\n"^n^" is: " :: (map (Pretty.string_of o pretty_thm ctxt) ts))
         | NONE => [Pretty.str ("\n"^n^": has no induction scheme")]))  thinds))*)
      (*val schemes = map (the o snd) (filter (Basics.is_some o snd) thinds)*)
    in
      ALLGOALS(try_induct_schemes ctxt (induct_simp_or_metis (facts,lemmas))) thm
    end;

(* An induction tactic to paste into the proof-script afterwards *)
fun induct_simp_tac ctxt thm = 
    let   
      val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
      val ctxt' = Library.foldl (fn (ctxt,thm) => Simplifier.add_simp thm ctxt)
                                (ctxt, lemmas)
    in 
      ALLGOALS(try_inductable_vars ctxt' (induct_and_simp lemmas)) thm
    end;

end;

(*-----------------------------------------------------------------------------------------*)
(* Structures for pre-defined combinations of routine/hard reasoning in Hipster            *)
(*-----------------------------------------------------------------------------------------*)

signature EXPL_TACS =
sig
  val routine_tac : Proof.context -> tactic
  val routine_tac_str : string
  val hard_tac : Proof.context -> tactic
  val final_tactic_str : Proof.context -> string
end


(* This structure considers simplification or FO reasoning by Metis as routine. *)
(* Proofs requiring structural induction is considered as "hard"                *)
structure Simp_Metis_T : EXPL_TACS =
struct

fun routine_tac ctxt = DEPTH_SOLVE (
       Ind_Tacs.simp_or_metis ctxt (ThyExpl_Data.facts_of_ctxt ctxt, 
                                    ThyExpl_Data.proved_of_ctxt ctxt @ Hipster_Rules.get ctxt));

val routine_tac_str = "by (tactic {* Simp_Metis_Tacs.routine_tac @{context} *})"; 

fun hard_tac ctxt =
    let
      val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
      val facts = ThyExpl_Data.facts_of_ctxt ctxt
    in
      ALLGOALS (Ind_Tacs.try_inductable_vars ctxt 
                                            (Ind_Tacs.induct_simp_or_metis (facts,lemmas)))
    end; 

(* The fact_nms are names of extra theorems that we want to refer to in the output *)
fun final_tactic_str ctxt =
    let
    (* val thy_expl_thms =  map (fn thm => Long_Name.base_name(Thm.get_name_hint thm)) 
                               (Hipster_Rules.get ctxt); *)
      (* Only need to pass the facts, the thy_expl theorems are looked up by the tactic *)
      val facts_str = Library.space_implode " " (ThyExpl_Data.fact_names_of_ctxt ctxt)
                                                 
    in 
      "by (hipster_induct_simp_metis " ^ facts_str ^")"
    end;
end


(* Induction with schemes! *)
structure Ind_Schemes_T : EXPL_TACS =
struct

fun routine_tac ctxt = DEPTH_SOLVE (
       Ind_Tacs.simp_or_metis ctxt (ThyExpl_Data.facts_of_ctxt ctxt,
                                    ThyExpl_Data.proved_of_ctxt ctxt @ Hipster_Rules.get ctxt));
val routine_tac_str = "by (tactic {* Ind_Schemes_Tacs.routine_tac @{context} *})"; 

fun hard_tac ctxt = 
    let
      val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
      val facts = ThyExpl_Data.facts_of_ctxt ctxt
    in
      ALLGOALS(Ind_Tacs.try_induct_schemes ctxt (Ind_Tacs.induct_simp_or_metis (facts,lemmas)))
    end;

fun final_tactic_str ctxt =
    let
      val facts_str = Library.space_implode " " (ThyExpl_Data.fact_names_of_ctxt ctxt)
      (* TODO: change so as to have the top level extract the appropriate induction scheme rules? *)
    in
      "by (hipster_induct_schemes " ^ facts_str ^")"
    end;
end


structure Simp_T : THY_EXPL_TACS =
struct

fun routine_tac ctxt =
     let
       val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
     in
        SOLVE (Ind_Tacs.prove_by_simp ctxt lemmas)
     end;

val routine_tac_str = "by (tactic {*Simp_Tacs.routine_tac @{context}*})";

fun hard_tac ctxt =
    let
      val lemmas = ThyExpl_Data.proved_of_ctxt ctxt @ Hipster_Rules.get ctxt
    in
      ALLGOALS (Ind_Tacs.try_inductable_vars ctxt (Ind_Tacs.induct_and_simp lemmas))
    end;

(* The fact_nms are names of extra theorems that we want to refer to in the output *)
fun final_tactic_str _ = "by hipster_induct_simp"

end


