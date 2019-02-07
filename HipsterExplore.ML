(*  Authors:     Moa Johansson, Chalmers University of Technology
                 Irene Lobo Valbuena, Chalmers University of Technology

Hipster theory exploration with QuickSpec 2 via tip-spec
*)

(* Call the QuickSpec 2 theory exploration system. Prove the resulting conjectures. Those provable by
   routine reasoning are deemed non-interesting and discarded. Those requiring "hard" reasoning are
   kept. *)

(* Re-factoring of Hipster_Explore to use ctactics and tracing proofs *)

structure Hipster_Explore (* : HIPSTER_THY_EXPLORATION *) =
struct

(*-----------------------------------------------------------------------------------------*)
(* Create a proof script for lemmas found.  *)
(*-----------------------------------------------------------------------------------------*)
fun proof_str ctxt proof_script name thm =
  let
    (* Print variables without ? *)
    val ctxt' = Config.put show_question_marks false ctxt
    val str_of_term =  Syntax.string_of_term ctxt'
    val lemma_str = Library.quote (str_of_term (Thm.prop_of thm))
    (*val name = Long_Name.base_name (Thm.get_name_hint thm)
    val _ = @{print} name *)
  in
    (* FIXME: Make keeping track of used names used better. Put in theory data instead of having tag *)
    "lemma " ^ name ^" [thy_expl]: " ^ lemma_str ^ "\n" ^ proof_script
  end

(*-----------------------------------------------------------------------------------------*)
(* The proof-loop, trying to prove the conjectures found by QuickSpec  *)
(* FIXME: Change so there is a hierarchy of tactics of increasing power (not just two),
   so each conjecture is tried with a weaker tactic before trying the harder tactics. *)
(*-----------------------------------------------------------------------------------------*)
fun try_nxt_conj ctxt =
  case (ThyExpl_Data.open_conjs_of_ctxt ctxt) of
    [] => (*retry open_conjs if we have some new proved since last time.*)
      if (ThyExpl_Data.progress_of_ctxt ctxt)
        then SOME (ctxt
                    |> ThyExpl_Data.set_open_conjs_ctxt (ThyExpl_Data.failed_of_ctxt ctxt)
                    |> ThyExpl_Data.set_failed_ctxt []
                    |> ThyExpl_Data.set_progress_ctxt false)
        else NONE

  | (c::cs) => (* try proving next open conj *)
      let
        val lemma_str = Syntax.string_of_term ctxt (Thm.concl_of c)
        val tacs = Tactic_Data.get_tacs (Proof_Context.theory_of ctxt)
        val _ = Hipster_Utils.maybe_output ctxt 50 ("Proving: "^lemma_str)
        val sl = tacs |> filter (fn tac => (Tactic_Data.get_applies_to tac) ctxt c)
                      |> map Tactic_Data.get_technique
        val _ = Hipster_Utils.maybe_output ctxt 60 ("Using techniques: "^String.concatWith " " sl)
        fun firstSome f g [] = NONE
          | firstSome f g (x::xs) = let val fx = f x in if g fx then SOME fx else firstSome f g xs
                                    end handle THM _ => firstSome f g xs
      in
        case (firstSome (fn s => SINGLE (Tactic_Data.routine_tac s ctxt) c) is_some sl) of (* Discard this, it is trivial *)
          SOME _ =>
            let val _ = Hipster_Utils.maybe_output ctxt 55 ("Trivial proof: "^lemma_str)
            in SOME (ThyExpl_Data.set_open_conjs_ctxt cs ctxt)
            end
        | _ =>
            case firstSome (fn s => (s,CTac.SINGLE (Tactic_Data.hard_ctac s ctxt) (ctxt,c))) (is_some o snd) sl of
              SOME(s,SOME (ctxt1, proved_thm)) =>
                let
                  val (new_nm, ctxt') = ThyExpl_Data.fresh_name ctxt1
                  val proof_script = proof_str ctxt' (Tactic_Data.hard_tac_str s ctxt') new_nm proved_thm
                  val final_thm = proved_thm
                                    |> Drule.generalize
                                      (Hipster_Utils.frees_and_tfrees_of_thm proved_thm)
                                    |> Goal.finish ctxt'
                                    |> Thm.put_name_hint new_nm

                  (*val gen_thm = Runtime.exn_trace (fn () => Drule.generalize
                            (Hipster_Utils.frees_and_tfrees_of_thm final_thm) final_thm)*)
                  val _ = Hipster_Utils.maybe_print ctxt' 25
                            ("Proved: " ^ lemma_str)
                in
                  SOME (ctxt'
                          |> snd o Local_Theory.note ((Binding.name new_nm,[]), [final_thm])
                          |> ThyExpl_Data.set_open_conjs_ctxt cs
                          |> ThyExpl_Data.add_proved_ctxt ((*Thm.put_name_hint new_nm *)final_thm)
                          |> ThyExpl_Data.set_progress_ctxt true
                          |> ThyExpl_Data.add_proof_script_ctxt (new_nm, proof_script))
                end
            (* NONE indicates that the tactic failed to prove c, put back with open_conjs *)
            | _ =>
                let val _ = Hipster_Utils.maybe_output ctxt 55 ("Failed proving: "^lemma_str)
                in SOME (ctxt
                          |> ThyExpl_Data.set_open_conjs_ctxt cs
                          |> ThyExpl_Data.add_failed_ctxt c)
                end
      end


fun proof_loop ctxt cand_lemmas_str =
  let
    (* Split long string with conjectures (blank lines in between),
       after merge long ones split over two lines. *)
    fun merge_split_eqs [] = []
      | merge_split_eqs [x] = if (x="") then [] else [x]
      | merge_split_eqs (x::y::rest) =
        if (y="")
        then x::merge_split_eqs (y::rest) else (merge_split_eqs (x^y::rest))

    val conjs = cand_lemmas_str
                |> Library.split_lines
                |> merge_split_eqs

    val ctxt1 = ThyExpl_Data.init_expl ctxt [] [] NONE conjs

    fun recf ctxt =
      case (try_nxt_conj ctxt) of
        NONE => ctxt
      | SOME ctxt' => recf ctxt'
  in
    recf ctxt1
  end

(*------------------------------------------------------------------------------------------------*)
(* Get names of functions which Isabelle's code generator translates to Haskell Prelude functions *)
(*------------------------------------------------------------------------------------------------*)
fun map_to_haskell isa_nm =
  let
    val prelude_funs = [("List.rev", "Prelude.reverse"), ("List.append","Prelude.++"),
                        ("List.list.map", "Prelude.map"), ("Fun.comp","Prelude.."),
                        ("Fun.id", "Prelude.id")];
    in
      case (Library.find_first (fn (nm,_) => nm = isa_nm) prelude_funs) of
        NONE => Long_Name.base_name isa_nm
      | SOME (_,hs_nm) => hs_nm
  end;

(*-----------------------------------------------------------------------------------------*)
(* Call QuickSpec 2 (via tip-spec command-line tool)                                       *)
(*-----------------------------------------------------------------------------------------*)

fun tipspec_plain file consts obs ctxt =
  let
  val consts_str = Library.space_implode "," (map map_to_haskell consts)
  val add_funs =  " -k " ^ consts_str
  val to_explore = " -f " ^ consts_str
  val split_bool_eqs_flag = if (Misc_Data.split_bool_eqs ctxt) (* if we want to split boolean eqs to implications. *)
                       then "--simplify-gently --split-formulas " else "";
  in Hipster_Setup.tipGHC_cmd ^ file ^ add_funs ^ " | " ^ Hipster_Setup.tipSpec_cmd ^ to_explore ^ " " ^
      obs ^ " | " ^ Hipster_Setup.tipTransl_cmd ^ split_bool_eqs_flag
end

fun tipspec_explore ctxt cond_opt obs_opt const_nms =
  let
    val thy = Proof_Context.theory_of ctxt
    val thynm = Context.theory_name thy
    val outfile = Hipster_Setup.filepath^ (Context.theory_name thy) ^".hs"
    val obs_str = case obs_opt of false => ""
                               |  true  => "-o "

    val tipspec_cmd = case cond_opt of NONE => tipspec_plain outfile const_nms obs_str ctxt
                                     | SOME _ => raise ERROR "Conditionals not yet supported in this version."
                                      (*hipspec_cond c const_nms' outfile *)
    val path_opt = SOME (Path.explode Hipster_Setup.filepath);

    (* Stolen from Isabelle_system, massaged to not emit warnings*)
    fun my_bash_output s =
    let
      val {out, err, rc, ...} = Bash.process s;
      val _ = Hipster_Utils.maybe_output ctxt 20 err
    in (out, rc) end;

    val _ = Code_Target.export_code ctxt false const_nms [((("Haskell",thynm), path_opt), [])];
  in
       fst (my_bash_output tipspec_cmd)
  end;

(*-----------------------------------------------------------------------------------------*)
(* Start theory exploration and then output lemmas and their proof scripts.                 *)
(*-----------------------------------------------------------------------------------------*)

fun mk_lemma_str ctxt thm =
  let
    val name = Long_Name.base_name (Thm.get_name_hint thm)
    val proof_script =
        case (ThyExpl_Data.proof_script_of_thm name ctxt) of
          NONE => proof_str ctxt "oops" name thm
       |  SOME proof => proof
  in
    proof_script
  end

(* Outputs snippets of proof script with the discovered lemmas,
   that can be pasted into the theory file. *)
fun explore' cond_opt obs_opt ctxt const_nms =
  let
    val conjs = tipspec_explore ctxt cond_opt obs_opt const_nms
    val res_ctxt = proof_loop ctxt conjs
    val output = Library.space_implode "\n\n"
                (map (mk_lemma_str res_ctxt)
                    ((ThyExpl_Data.proved_of_ctxt res_ctxt)
                    @ (ThyExpl_Data.failed_of_ctxt res_ctxt)))
  in
    (res_ctxt, Hipster_Utils.maybe_print ctxt 0
                    (Active.sendback_markup_command output))
  end

val explore = explore' NONE false;
(* TODO: Hook for conditionals into QuickSpec 2. Currently not available. *)
fun explore_cond cond = explore' cond false;

val explore_obs = explore' NONE true;


(*-----------------------------------------------------------------------------------------*)
(* Theory exporation from an ongoing proof: Find lemmas to solve this subgoal              *)
(*-----------------------------------------------------------------------------------------*)

(* A tactic which picks up the constants from a subgoal, and applies theory exploration on these
   The aim is to find lemma(s) which allows for the goal to be proved. *)
fun explore_goal ctxt const_nms thm =
  let
      (* FIXME: When the context comes from and ongoing proof attempt,
         it might already have variables with bound types! If another lemma
         happen to use the same var name, you get an error. *)
      val res_ctxt =(* proof_loop_w_prio ctxt (SOME thm) *)
                       proof_loop ctxt
                      (tipspec_explore ctxt NONE false const_nms)
      val _ = Hipster_Utils.maybe_print ctxt 100 ("End of proof loop.")
      val lemma_list = ThyExpl_Data.proved_of_ctxt res_ctxt
      val lemmas = Library.space_implode "\n\n"
                          (map (mk_lemma_str res_ctxt) lemma_list)
  in
    case lemma_list of
      [] =>
        let val _ = Hipster_Utils.maybe_print ctxt 25 ("Failed to find lemmas which will prove goal.")
        in no_tac thm end
    | _ => (* Success, provided the explored lemmas, the thm can be proved. *)
        let
          (* val _ = writeln ("Try first proving lemmas:\n\n" ^ lemmas ^ "\n\n" ^
                             "Use these prove the open goal "^ (@{make_string} thm) ^ " " ^
                             (Tactic_Data.routine_tac_str res_ctxt))
          *)
        in
          Seq.single thm
        end
  end

end;
