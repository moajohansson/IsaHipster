(*  Author:     Moa Johansson, Chalmers University of Technology

Hipster theory exploration information about what tactic succeeded in a proof attempt.
*)

(*-----------------------------------------------------------------------------------------*)
(* Data recording choices in inductive proofs *)
(*-----------------------------------------------------------------------------------------*)

structure Induction_Data =
struct

(* Add proof methods that can be use by Hipster in Proof scripts. In addition to what comes from
    Sledgehammer, Hipster can merge simp calls to simp_all. *)
datatype Hipster_Proof_Method =
      Sledgehammer_Meth of Sledgehammer_Proof_Methods.proof_method
   |  Simp_All_Meth

 fun string_of_meth ctxt (m,facts) =
      case m of Sledgehammer_Meth meth =>
          (
            case meth of
             (* FIXME: If this is a method that acts on all subgoal, like auto, we might get a
             faulty proof script, unless we take this into account! Furthermore, the string
             might not fit into an apply-style script, e.g. apply (auto some_facts) isn't allowed
             in Isabelle. It should say something like "using fact by auto" or "using fact apply auto" *)
              Sledgehammer_Proof_Methods.Auto_Method => if (null facts) then "apply auto"
                                                        else "using " ^ space_implode " " facts  ^ " apply auto"
              | Sledgehammer_Proof_Methods.Blast_Method => if (null facts) then "apply blast"
                                                           else "using " ^ space_implode " " facts  ^ " apply blast"
              | Sledgehammer_Proof_Methods.Fastforce_Method => if (null facts) then "apply fastforce"
                                                           else "using " ^ space_implode " " facts  ^ " apply fastforce"
              | _ => "apply " ^ Sledgehammer_Proof_Methods.string_of_proof_method ctxt facts meth ^""
          )
           | Simp_All_Meth => "apply " ^ (if (null facts) then "simp_all"
                                         else "(simp_all add: " ^ space_implode " " facts)
datatype T = Data of
  { induction_rule : string option,
    induction_vars : string list,
    arbitrary_vars : string list,
    subgoal_tacs_strs :
      ((Hipster_Proof_Method * string list) list) Inttab.table
  }

fun get_induction_rule (Data d) = (#induction_rule d)
fun get_induction_vars (Data d) = (#induction_vars d)
fun get_subgoal_tac_strs (Data d) = (#subgoal_tacs_strs d)

fun update_induction_rule f (Data d) = Data{induction_rule = f (#induction_rule d),
                                       induction_vars = #induction_vars d,
                                       arbitrary_vars = #arbitrary_vars d,
                                       subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_induction_vars f (Data d) =  Data{induction_rule = #induction_rule d,
                                       induction_vars = f (#induction_vars d),
                                       arbitrary_vars = #arbitrary_vars d,
                                       subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_arbitrary_vars f (Data d) =  Data{induction_rule = #induction_rule d,
                                       induction_vars = #induction_vars d,
                                       arbitrary_vars = f (#arbitrary_vars d),
                                       subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_subgoal_tac_strs f (Data d) = Data{induction_rule = #induction_rule d,
                                       induction_vars = #induction_vars d,
                                       arbitrary_vars = #arbitrary_vars d,
                                       subgoal_tacs_strs = f (#subgoal_tacs_strs d)}

fun set_induction_rule rule = update_induction_rule (K rule)
fun set_induction_vars vars = update_induction_vars (K vars)
fun set_arbitrary_vars vars = update_arbitrary_vars (K vars)
fun set_subgoal_tac_strs tacs = update_subgoal_tac_strs (K tacs)

(* Need to store subgoal numbers tactic was applied to, for correct ordering.
   This is as we use ALL_GOALS sometimes, which work backwards (highest subgoal number first)) *)
fun add_subgoal_tac (sg_number, tac) =
  update_subgoal_tac_strs (Inttab.insert_list (fn _ => false) (sg_number, tac))


(* Induction rule NONE defaults to structural induction, as per Isabelle's induction tactic *)
val empty = Data{induction_rule = NONE, induction_vars = [],
                  arbitrary_vars = [], subgoal_tacs_strs = Inttab.empty}

fun get_proof_script (Data d) ctxt =
  let
  val simp_meth = Sledgehammer_Meth (Sledgehammer_Proof_Methods.Simp_Method)

  fun is_simp m = (m=Simp_All_Meth orelse m=simp_meth)

  (* If the same subgoal has several consecutive application of e.g. simp, then them and merge facts added *)
   fun merge_same_meths_sg i ms new_m =
       case ms of [] => new_m
        | [(m,fs)] => new_m @ [(m,fs)]
        | ((m1,f1)::(m2,f2)::ms) =>
              if (m1=simp_meth andalso m2=simp_meth)
              then merge_same_meths_sg i ((simp_meth, distinct (op =) f1@f2)::ms) new_m
              else merge_same_meths_sg i ((m2,f2)::ms) (new_m @ [(m1,f1)])

  (* FIXME: Only do if EACH subgoal has Simp as first tactic *)
  (* FIXME 2: For methods like auto/blast which work on all goals by default, also check this,
      otherwise include some subgoal-specific stuff *)
  fun merge_same_meths ms new_m =
      case ms of [] => new_m
          | [(m,fs)] => new_m @ [string_of_meth ctxt (m,fs)]
          | ((m1,f1)::(m2,f2)::ms) =>
              if (is_simp m1 andalso is_simp m2)
              then merge_same_meths ((Simp_All_Meth, distinct (op =)(f1@f2))::ms) new_m
              else merge_same_meths ((m2,f2)::ms) (new_m @ [string_of_meth ctxt (m1,f1)])

  val tac_table = (#subgoal_tacs_strs d)
                   |> Inttab.map (fn sg_meths => merge_same_meths_sg sg_meths [])
  (* For each subgoal, tactic applications is stored in reversed order, due to how Inttab works.*)
  val subgoal_tacs =  map (rev o snd) (Inttab.dest tac_table)

  fun mk_ind_str [] = ""
    | mk_ind_str vars_list =
      let
      val vars = String.concatWith " " vars_list
      val vars' = case (#arbitrary_vars d) of
                        [] => vars
                        | arb_vs => vars ^ " arbitrary: " ^ String.concatWith " " arb_vs
      val induction = "apply (induct "
      in
        (case (#induction_rule d) of
          NONE => induction ^ vars' ^ ")\n"
          | SOME rule => induction ^ vars' ^ " rule: " ^ rule ^ ")\n")
      end;

 fun mk_app_str meths s =
    case meths of
      [] => s ^ "done"
    | (m::ms) => mk_app_str ms (s ^ (string_of_meth ctxt m) ^"\n")
       (*let val meth_str = string_of_meth ctxt m
       in *)
       (*if (null ms)
          then s ^ "by " ^ m
          else mk_app_str ms (s ^ "apply " ^ m ^"\n") *)
  in
     (* mk_ind_str (#induction_vars d) ^ (mk_app_str (merge_same_meths (flat subgoal_tacs) []) "") *)
      mk_ind_str (#induction_vars d) ^ (mk_app_str (flat subgoal_tacs)) ""
  end;

structure IndData = Proof_Data (type T = T
                                fun init _ = empty)

(* Getting and setting IndDate of a context *)
val induction_rule_of_ctxt = get_induction_rule o IndData.get
val induction_vars_of_ctxt = get_induction_vars o IndData.get
val subgoal_tac_strs_of_ctxt = get_subgoal_tac_strs o IndData.get

fun set_induction_rule_ctxt rule ctxt =
  IndData.put (set_induction_rule rule (IndData.get ctxt)) ctxt
fun set_induction_vars_ctxt vars ctxt =
  IndData.put (set_induction_vars vars (IndData.get ctxt)) ctxt
fun set_arbitrary_vars_ctxt arb_vars ctxt =
  IndData.put (set_arbitrary_vars arb_vars (IndData.get ctxt)) ctxt
fun set_subgoal_tac_strs_ctxt tacs ctxt =
  IndData.put (set_subgoal_tac_strs tacs (IndData.get ctxt)) ctxt

fun add_subgoal_tac_ctxt tac ctxt =
  IndData.put (add_subgoal_tac tac (IndData.get ctxt)) ctxt

val reset_ind_proof_data_ctxt = IndData.put empty

fun get_proof_script_ctxt ctxt = get_proof_script (IndData.get ctxt) ctxt

end
