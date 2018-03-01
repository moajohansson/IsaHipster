(*  Author:     Moa Johansson, Chalmers University of Technology
    Author:     Irene Lobo Valbuena, Chalmers University of Technology

Hipster utility functions for extracting term information.
*)

(* Various utility functions for Hipster *)

signature HIPSTER_UTILS =
sig
  val typ_tfrees_of : Term.typ -> (string * sort) list
  val thy_consts_of : string -> Thm.thm -> string list
  val frees_of : Term.term -> (string * Term.typ) list
  val frees_and_tfrees_of_thm : Thm.thm -> string list * string list
  val add_term_frees : Term.term * Term.term list -> Term.term list

  val dangling_vars : Term.term -> (string * Term.typ) list * (string * Term.typ) list
  val types_in_term : Term.term -> typ list
  val type_names : Term.term -> string list
  val inductible_types : Term.term -> Proof.context -> string list
  val coinductible_types : Term.term -> Proof.context -> string list

  val maybe_output : Proof.context -> int -> string -> unit
  val maybe_print : Proof.context -> int -> string -> unit
  val maybe_print_any : Proof.context -> int -> 'a -> unit
  val maybe_pretty : Proof.context -> int -> Pretty.T -> unit
end


structure Hipster_Utils : HIPSTER_UTILS =
struct

(*------------------------------------------------------------------------------------*)
(* Term mainipulation stuff, stolen from IsaPlanner... *)
(*------------------------------------------------------------------------------------*)

fun add_term_frees (t, frees: Term.term list) =
  case t of
    Free _          => Ord_List.insert Term_Ord.term_ord t frees
  | Abs (_,_,body)  => add_term_frees(body,frees)
  | f$t             => add_term_frees (f, add_term_frees(t, frees))
  | _               => frees

fun add_typ_tfrees (Type(_,Ts),fs)  = List.foldr add_typ_tfrees fs Ts
  | add_typ_tfrees (TFree(f),fs)    = insert (op =) f fs
  | add_typ_tfrees (TVar(_),fs)     = fs

fun frees_of t = map Term.dest_Free (add_term_frees (t,[]))
fun typ_tfrees_of ty = add_typ_tfrees(ty,[])

(* Get a pair of (type-frees, term frees) without dups. *)
fun frees_and_tfrees_of_thm thm = 
  let val t = Thm.concl_of thm
  in
    (map fst (typ_tfrees_of (Term.fastype_of t)), map fst (frees_of t))
  end

fun maybe_output ctxt verbosity_threshold =
  if Misc_Data.verbosity ctxt >= verbosity_threshold then
    Output.tracing
  else K ()

fun maybe_print ctxt verbosity_threshold =
  if Misc_Data.verbosity ctxt >= verbosity_threshold then
     writeln
  else K ()

fun maybe_print_any ctxt verbosity_threshold x =
  if Misc_Data.verbosity ctxt >= verbosity_threshold then
    let val _ = @{print} x in () end
  else ()

fun maybe_pretty ctxt verbosity_threshold =
  if Misc_Data.verbosity ctxt >= verbosity_threshold then
    Pretty.writeln
  else K ()

fun add_consts_of_thy (thynm, t) consts =
  case t of
    (* FIXME: for now we remove those logic theories we know will be present : need to find a way
              of having "included" "own" theories *)
    Const (nm,_)   => if (String.isPrefix "Pure" nm orelse String.isPrefix "HOL" nm)
                        then consts
                        else insert (op =) nm consts
  | Abs (_,_,body) => add_consts_of_thy (thynm,body) consts
  | t1$t2          => add_consts_of_thy (thynm, t1) (add_consts_of_thy (thynm,t2) consts)
  | _              => consts

(* Get all constants in this thm which are defined in the given theory *)
fun thy_consts_of thynm thm = add_consts_of_thy (thynm, Thm.concl_of thm) []


(*------------------------------------------------------------------------------------*)
(* Variable and type extraction utilities *)
(*------------------------------------------------------------------------------------*)

(* Gives all sinks in a term; separates them into (free variables, universally quantified)
   These are given along with their types *)
fun dangling_vars t = (Term.add_frees t [], Term.strip_all_vars t)

(* Collects all types appearing in a term *)
fun types_in_term t = case t of
    Bound _     => []
  | Free (_,T)  => [T]
  | Const (_,T) => [T]
  | Var (_,T)   => [T]
  | Abs (_,T,b) => T::types_in_term b (* XXX: insert *)
  | f$a         => types_in_term f @ types_in_term a

(* Collects all type names (base, parameterised constructors or higher order operators)
   occurring in a term *)
fun type_names t =
  let fun name_of T = [(fst o dest_Type) T]
                        handle _ => []
      fun names_in (args, T) = name_of T @ (List.concat (map name_of args))
      fun sieve tn = not (String.isPrefix "Pure" tn orelse String.isPrefix "HOL" tn orelse "prop"= tn)
  in
    map (names_in o strip_type) (distinct (op =) (types_in_term t))
      |> List.concat
      |> filter sieve o distinct (op =)
  end

fun inductible_types t ctxt =
  filter (fn t => is_some(Proof_Context.lookup_fact ctxt (t^".induct")))  (type_names t)

fun coinductible_types t ctxt =
  filter (fn t => is_some(Proof_Context.lookup_fact ctxt (t^".coinduct")))  (type_names t)

end
(*
val yup = @{term "!! x. x=y"}
val tup = @{term "\<lambda> x . (\<lambda> y . x y) "}
val sup = @{term "x = z (y t) (\<lambda> f. f r)"}

val x1 = Term.add_frees sup []
val x2 = Term.strip_all_vars sup*)

