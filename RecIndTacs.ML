(*  Author:     Moa Johansson, Chalmers University of Technology

Hipster recursion induction tactics.


Recursion induction should be considered when:
There is a suitable function with a recursion induction theorem,
and the arguments of the functions are variables.


*)

signature REC_IND_TACS =
  sig
    val inductable_pos_of_funs: Proof.context -> thm -> (Zipper.T * Zipper.T list * (string * thm list)) list
    val recinduct_simp: Proof.context -> thm -> thm Seq.seq
    val recinduct_simp_or_sledgehammer: Proof.context -> thm -> thm Seq.seq
    val try_recinduct: (Proof.context -> tactic) -> Proof.context -> thm -> thm Seq.seq
  end

structure Rec_Ind_Tacs (* : REC_IND_TACS *)  =
struct

(* z is a Zipper located at a candidate function position. Here,
   we check if this position is suitable, i.e. if there are variables
   in the argument positions. *)
fun is_rec_ind_applicable (z,rec_ind_thm) = 
  let
 (* n is the number of args to the function in the focus of the zipper.
    Returns a list of zippers with focus on the arguments instead (if possible). *)
  fun zip_to_args 0 _ args = SOME (rev args) (* args in left-right order as appear in term *)
    | zip_to_args n z args = 
      let 
        val z' = Zipper.move_up z 
      in    
        zip_to_args (n-1) z' ((Zipper.move_down_right z') :: args)    
      handle Zipper.move _ => NONE
      end;
  in
  case z of 
   (Const(_,ty),_) => 
            (let 
                (* Find location of the arguments of the constant (a function) we're interested 
                   in possibly applying rec induction for *)
                val zip_args = zip_to_args (length (fst (Term.strip_type ty))) z []
            in 
              (* Check if args are variables, if so recursion induction is applicable directly. *)
               case zip_args of 
                  NONE => NONE
                  | SOME args =>             
                        if (List.all (fn z => Term.is_Free (Zipper.trm z)) args)
                        then SOME(z,args,rec_ind_thm) else NONE
            end)
   | _ => NONE
  end;


(* Finds positions where recursion induction is applicable + vars + induction thm *)
fun inductable_pos_of_funs ctxt thm  =
  let
    val thm_zip = Zipper.mktop (Thm.concl_of thm); 
    val all_leaves = Seq.list_of (ZipperSearch.leaves_lr thm_zip);

    (* positions of functions  with a rec. induction theorem. *)
    fun inductable_fun_in_zipper z =
      case z of 
      (Const(cnm,_),_) => 
          let val recind_nm = cnm^".induct"
          in  
          SOME (z, (recind_nm, (Sledgehammer_Util.thms_of_name ctxt recind_nm)))
          handle ERROR _ =>  NONE
          end
      | _ => NONE; 

    val all_inductable_funs = map_filter inductable_fun_in_zipper all_leaves;

    val inductable_pos = map_filter is_rec_ind_applicable all_inductable_funs
  in
    inductable_pos  
  end;

(* Tactic for trying recursion induction. Will try all positions where a function f
    has variables as arguments (and f has a recursion induction theorem). Returns 
   the first possibility which returns a successful proof. *)
fun try_recinduct subgoal_tac ctxt thm =
  let 
    val rec_inds =  inductable_pos_of_funs ctxt thm
    val poss_inds = map (fn(_, varz, recind_thm) => 
                          let 
                            val vars = map (fn z => Zipper.trm z |> Term.dest_Free |> fst) varz
                            (*val _ = @{print} vars*) (* just for testing during dev.*)
                          in
                            DEPTH_SOLVE (
                              (Seq.DETERM 
                                (HEADGOAL  
                                  (Ind_Tacs.induct_on_var_tac ctxt (SOME recind_thm) (SOME vars))))
                               THEN 
                             (*  (Ind_Tacs.simp_or_sledgehammer_tac ctxt)) *)
                               subgoal_tac ctxt)
                          end) rec_inds 
  in
    FIRST (poss_inds) thm
  end;

val recinduct_simp = try_recinduct (fn ctxt => Ind_Tacs.prove_by_simp ctxt []);
val recinduct_simp_or_sledgehammer = try_recinduct Ind_Tacs.simp_or_sledgehammer_tac
end;