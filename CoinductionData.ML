(*  Author:     Sólrún Einarsdóttir, Chalmers University of Technology

    Hipster theory exploration information records about what choices
    succeeded in an attempt at a coinductive proof. Much borrowed from
    InductionData.ML.
*)

structure Coinduction_Data =
struct
datatype T = Data of
  { coinduction_rule : string option,
    arbitrary_vars : string list,
    subgoal_tacs_strs :
      ((Induction_Data.Hipster_Proof_Method * string list) list) Inttab.table
  }
fun get_coinduction_rule (Data d) = (#coinduction_rule d)
fun get_subgoal_tac_strs (Data d) = (#subgoal_tacs_strs d)

fun update_coinduction_rule f (Data d) = Data{coinduction_rule = f (#coinduction_rule d),
                                                arbitrary_vars = #arbitrary_vars d,
                                             subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_arbitrary_vars f (Data d)   = Data{coinduction_rule = #coinduction_rule d,
                                                arbitrary_vars = f (#arbitrary_vars d),
                                             subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_subgoal_tac_strs f (Data d) = Data{coinduction_rule = #coinduction_rule d,
                                                arbitrary_vars = #arbitrary_vars d,
                                             subgoal_tacs_strs = f (#subgoal_tacs_strs d)}

fun set_coinduction_rule rule = update_coinduction_rule (K rule)
fun set_arbitrary_vars vars = update_arbitrary_vars (K vars)
fun set_subgoal_tac_strs tacs = update_subgoal_tac_strs (K tacs)

(* FIXME: Need to store subgoal numbers tactic was applied to, for correct ordering.
   This is as we use ALL_GOALS sometimes, which work backwards (highest subgoal number first)) *)
fun add_subgoal_tac (sg_number, tac) =
  update_subgoal_tac_strs (Inttab.insert_list (fn _ => false) (sg_number, tac))


val empty = Data{coinduction_rule = NONE, arbitrary_vars = [], subgoal_tacs_strs = Inttab.empty}

fun get_proof_script (Data d) ctxt =
  let
  val tac_table = (#subgoal_tacs_strs d)
  val subgoal_tacs = map (rev o snd) (Inttab.dest tac_table)
  val arbs = case (#arbitrary_vars d) of
                        [] => ""
                        | arb_vs => "arbitrary: " ^ String.concatWith " " arb_vs
  val app_coind = "(coinduction "

  fun dequalify ctxt s =
    let val thystr = Context.theory_name (Proof_Context.theory_of ctxt) ^ "." in
     if size s >= size thystr andalso thystr = String.substring(s,0,size thystr) then
      let val newstr = String.substring(s,size thystr, size s - size thystr) in
        if can (Proof_Context.get_thm ctxt) newstr then newstr else s
      end
     else s
    end

  val coind_str = case (#coinduction_rule d) of
          NONE => app_coind ^ arbs ^ ")\n"
          | SOME rule => app_coind ^ arbs ^ " rule: " ^ dequalify ctxt rule ^ ")\n"

  fun is_simp m = (m = Induction_Data.Simp_All_Meth orelse
                   m = Induction_Data.Sledgehammer_Meth
                       (Sledgehammer_Proof_Methods.Simp_Method))

(*  fun merge_same_meths ms new_m =
      case ms of [] => new_m
          | [(m,fs)] => new_m @ [Induction_Data.string_of_meth ctxt (m,fs)]
          | ((m1,f1)::(m2,f2)::ms) =>
              if (is_simp m1 andalso is_simp m2)
              then merge_same_meths ((Induction_Data.Simp_All_Meth,f1@f2)::ms) new_m
              else merge_same_meths ((m2,f2)::ms) (new_m @ [Induction_Data.string_of_meth ctxt (m1,f1)])
*)
 val app_strs = map (Induction_Data.string_of_meth ctxt) (flat subgoal_tacs)

 fun split_longest_id_suffix [] = ([],[])
   | split_longest_id_suffix (f::l) =
     case split_longest_id_suffix l of
       ([],[]) => ([],[f])
     | (f1::l1,l2) => (f::f1::l1,l2)
     | ([],f2::l2) => if f = f2 then ([],f::f2::l2)
                      else ([f],f2::l2)

 fun merge_app_strs aps =
    let val (a1,a2) = split_longest_id_suffix aps
    in if length a2 > 1 then
           a1 @ [hd a2^"+"]
         else
           aps
    end

  fun split_proof_str s =
   let val splt = String.tokens (curry op = #" ") s
   in
     case splt of 
       "using"::l => 
       let val (facts,script) = Library.take_prefix (not o curry op = "apply") l
       in (facts,String.concatWith " " (tl script)) end
     | "apply"::l=> ([],String.concatWith " " l)
     | _ => raise Domain
   end
  in
    case merge_app_strs app_strs of
      [e] => (case split_proof_str e of 
                ([],proof) => " by "^coind_str^"    "^proof
              | (facts,proof) =>
                (case #coinduction_rule d |> Option.map (Proof_Context.get_thm ctxt)
                      |> Option.map Rule_Cases.get |> Option.map fst 
                   of SOME [((case_string,_),_)] =>
                       "proof"^coind_str
                      ^"  case "^case_string ^ " thus ?case\n    using "
                      ^String.concatWith " " facts^"\n    by "^proof^"\nqed"
                    | _  => "apply "^ coind_str ^ e ^ "\ndone"))
    | l => "apply "^coind_str ^ String.concatWith "\n" l ^ "\ndone"
  end;

structure CoIndData = Proof_Data (type T = T
                                  fun init _ = empty)

(* Getting and setting CoIndData of a context *)
val coinduction_rule_of_ctxt = get_coinduction_rule o CoIndData.get
val subgoal_tac_strs_of_ctxt = get_subgoal_tac_strs o CoIndData.get

fun set_coinduction_rule_ctxt rule ctxt =
  CoIndData.put (set_coinduction_rule rule (CoIndData.get ctxt)) ctxt
fun set_arbitrary_vars_ctxt arb_vars ctxt =
  CoIndData.put (set_arbitrary_vars arb_vars (CoIndData.get ctxt)) ctxt
fun set_subgoal_tac_strs_ctxt tacs ctxt =
  CoIndData.put (set_subgoal_tac_strs tacs (CoIndData.get ctxt)) ctxt

fun add_subgoal_tac_ctxt tac ctxt =
  CoIndData.put (add_subgoal_tac tac (CoIndData.get ctxt)) ctxt

val reset_coind_proof_data_ctxt = CoIndData.put empty

fun get_proof_script_ctxt ctxt = get_proof_script (CoIndData.get ctxt) ctxt

end
