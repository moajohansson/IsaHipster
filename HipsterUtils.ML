(* Various utility functions for Hipster *)

signature HIPSTER_UTILS =
sig 
  val typ_tfrees_of : Term.typ -> (string * sort) list 
  val thy_consts_of : string -> Thm.thm -> string list
  val frees_of : Term.term -> (string * Term.typ) list 
  val frees_and_tfrees_of_thm : Thm.thm -> string list * string list
end


structure Hipster_Utils : HIPSTER_UTILS =
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

fun add_consts_of_thy (thynm, t) consts = 
    case t of
      (* FIXME: for now we remove those logic theories we know will be present : need to find a way
                of having "included" "own" theories *)
      Const(nm,_) => if (String.isPrefix "Pure" nm (*orelse String.isPrefix "HOL" nm*))
                      then consts
                      else insert (op =) nm consts
    | Abs(_,_,body) => add_consts_of_thy (thynm,body) consts
    | t1$t2 => add_consts_of_thy (thynm, t1) (add_consts_of_thy (thynm,t2) consts) 
    | _ => consts;

(* Get all constants in this thm which are defined in the given theory *)
fun thy_consts_of thynm thm = 
      add_consts_of_thy (thynm, Thm.concl_of thm) [];


end
