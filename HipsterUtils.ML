(* Various utility functions for Hipster *)

signature HIPSTER_UTILS =
sig 
  val typ_tfrees_of : Term.typ -> (string * sort) list
  val thy_consts_of : string -> Thm.thm -> string list
  val frees_of : Term.term -> (string * Term.typ) list
  val frees_and_tfrees_of_thm : Thm.thm -> string list * string list

  val dangling_vars : Term.term -> (string * Term.typ) list * (string * Term.typ) list
  val type_names : Term.term -> string list
  val types_in_term : Term.term -> typ list
end

val yup = @{term "!! x. x=y"}
val tup = @{term "\<lambda> x . (\<lambda> y . x y) "}
val sup = @{term "x = z (y t) (\<lambda> f. f r)"}

val x1 = Term.add_frees sup []
val x2 = Term.strip_all_vars sup

structure Hipster_Utils : HIPSTER_UTILS =
struct

(*------------------------------------------------------------------------------------*)
(* Term mainipulation stuff, stolen from IsaPlanner... *)
(*------------------------------------------------------------------------------------*)

fun add_term_frees (t, frees: Term.term list) = let
      fun myeq tup = case Term_Ord.term_ord tup of EQUAL => true | _ => false in
    (case t of
      Free   _ => (*distinct myeq (t::frees)*) Ord_List.insert Term_Ord.term_ord t frees
      | Abs (_,_,body) => add_term_frees(body,frees)
      | f$t =>  add_term_frees (f, add_term_frees(t, frees))
      | _ => frees) end;

fun add_typ_tfrees (Type(_,Ts),fs) = List.foldr add_typ_tfrees fs Ts
      | add_typ_tfrees(TFree(f),fs) = insert (op =) f fs
      | add_typ_tfrees(TVar(_),fs) = fs;

fun frees_of t = map Term.dest_Free (add_term_frees (t,[]));
fun typ_tfrees_of ty = add_typ_tfrees(ty,[]);

(*
@{term "(a::nat) + b = c"}
> Const ("HOL.eq", ...) $
> (Const ("Groups.plus_class.plus", ...) $ ... $ ...) $ ...
datatype term =
  Const of string * typ
| Free of string * typ
| Var of indexname * typ
| Bound of int
| Abs of string * typ * term
| $ of term * term
*)

fun dangling_vars t = (Term.add_frees t [], Term.strip_all_vars t)

(* Get a pair of (type-frees, term frees) without dups. *)
fun frees_and_tfrees_of_thm thm = 
    let 
      val t = Thm.concl_of thm
    in (map fst (typ_tfrees_of (Term.fastype_of t)), map fst (frees_of t)) end;

fun add_consts_of_thy (thynm, t) consts = 
    case t of
      (* FIXME: for now we remove those logic theories we know will be present : need to find a way
                of having "included" "own" theories *)
      Const(nm,_) => if (String.isPrefix "Pure" nm orelse String.isPrefix "HOL" nm)
                      then consts
                      else insert (op =) nm consts
    | Abs(_,_,body) => add_consts_of_thy (thynm,body) consts
    | t1$t2 => add_consts_of_thy (thynm, t1) (add_consts_of_thy (thynm,t2) consts) 
    | _ => consts;

(* Get all constants in this thm which are defined in the given theory *)
fun thy_consts_of thynm thm = 
      add_consts_of_thy (thynm, Thm.concl_of thm) [];

fun types_in_term t = case t of
    Var (_,T)       => (*let val _ = @{print} "Var" in t end*) [T]
  | (f$a)           => (*let val _ = @{print} "$" in reP t end*) types_in_term f @ types_in_term a
  | (Abs (_, T, b)) => (*let val _ = @{print} "Abs" in t end*) T::(types_in_term b)
  | (Free (_, T))   => [T] (* TODO: Bound, Const *)
  | Bound _         => []
  | Const (_, T)    => [T];

fun type_names t =
  let
    fun  ddd T = [(fst o dest_Type) T]
                  handle _ => []
    fun names_in (args, T) = ddd T @ (List.concat (map ddd args)) (*(fst o dest_Type) T @ map (fst o dest_Type) args*)
    fun sieve tt = not (String.isPrefix "Pure" tt orelse String.isPrefix "HOL" tt orelse "prop"= tt)
  in
    filter sieve (distinct (op=) (List.concat (map (names_in o strip_type) (distinct (op =) (types_in_term t)))))
  end;
(*
val ll = distinct (op=) (List.concat (map (exx o strip_type) (distinct (op =) (reT eg2))));
fun ff tt =  not (String.isPrefix "Pure" tt orelse String.isPrefix "HOL" tt orelse String.isPrefix "prop" tt);
filter ff ll;*)

end
