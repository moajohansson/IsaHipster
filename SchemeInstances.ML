(*  Author:     Irene Lobo Valbuena, Chalmers University of Technology

Instantiations with variables for type signatures.
*)


signature SCHEME_INSTANCES =
sig
  type var_typ = string * Term.typ
  type instance = var_typ list
  type instance_bins = instance list list
  val empty_instance : instance_bins
  val var_typ_ord : var_typ * var_typ -> order
  val instances_for_with : typ list -> var_typ list -> instance_bins
  val flatten_instances : bool -> instance_bins -> instance list
end


structure Scheme_Instances : SCHEME_INSTANCES =
struct

type var_typ = string * Term.typ
type instance = var_typ list    (* a variable instantiation for some given type signature*)
type instance_bins = instance list list   (* collections of instances by size *)

fun var_typ_ord ((x,t1),(y,t2)) =
  case fast_string_ord (x,y) of
    EQUAL => (if Term_Ord.typ_ord (t1,t2) = EQUAL then EQUAL else raise Type.TYPE_MATCH)
  | LESS => LESS
  | GREATER => GREATER

val empty_instance = [[[]]]
val merge_n_instances = fold (Ord_List.insert (dict_ord var_typ_ord))

fun index_bins v (bin1s::bin0s::binss) =
      let val new1s = map (fn is0 => is0 @ [v] (*v::is0*)) bin0s
          val all1s = merge_n_instances new1s bin1s
      in all1s :: index_bins v (bin0s::binss) end
  | index_bins _ [[[]]] = [[[]]]
  | index_bins _ _      = []

(* TODO: extract elsewhere? *)
fun zipWith f xs ys = ListPair.foldr (fn (a, b, cs) => f(a, b)::cs) [] (xs, ys)
fun foldl1 _ nil     = raise Empty (* TODO: really raise error ? *)
  | foldl1 f (x::xs) = fold f xs x

(* Merges instance bins of the same length *)
fun merge_bins xss yss = zipWith (fn (xs,ys) => merge_n_instances ys xs) xss yss

fun fix_nth_arg (t::ts) xs bins =
      let fun update_types v = map (fn t' => if Term_Ord.typ_ord (t,t') = EQUAL then snd v else t') ts
          fun into_bins v = index_bins v ([]::bins)
          val vars = filter (fn v => Type.could_match (t, snd v)) xs
          val all_bins = map (fn v => fix_nth_arg (update_types v) (remove (op =) v xs) (into_bins v)) vars
      in if null all_bins then fix_nth_arg ts xs bins else foldl1 merge_bins all_bins end
  | fix_nth_arg [] _ bins = bins

(* Compute possible instances with given variables xs for a type signature ts (expressed as a list)
   Returns result as a list of bins according to instance size, with the most specific at the head *)
fun instances_for_with ts xs = fix_nth_arg ts xs empty_instance

(* true  => keep more specific instances in front
   false => keep looser instances in front *)
fun flatten_instances true bins  = List.concat bins
  | flatten_instances false bins = (List.concat o rev) bins

end

