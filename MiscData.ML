(*  Author:     Johannes Åman Pohjola, Chalmers University of Technology

Miscellaneous configuration data 
*)

(*-----------------------------------------------------------------------------------------*)
(* Data about tactics for hard/routine reasoning used for theory exploration *)
(*-----------------------------------------------------------------------------------------*)

structure Misc_Data =
struct

datatype T = Data of
  { verbosity : int, time : bool, hammer_timeout : string, split_bool_eqs : bool }


fun get_verbosity (Data d) = (#verbosity d);
fun get_hammer_timeout (Data d) = (#hammer_timeout d);
fun get_timing (Data d) = (#time d);
fun get_split_bool_eqs (Data d) = (#split_bool_eqs d);

fun update_verbosity f (Data d) =
  Data{verbosity = f (#verbosity d), time = #time d, hammer_timeout = #hammer_timeout d,
       split_bool_eqs = #split_bool_eqs d};
fun update_time f (Data d) =
  Data{verbosity = #verbosity d, time = f (#time d), hammer_timeout = #hammer_timeout d,
    split_bool_eqs = #split_bool_eqs d};
fun update_hammer_timeout f (Data d) =
  Data{verbosity = #verbosity d, time = #time d, hammer_timeout = f (#hammer_timeout d),
    split_bool_eqs = #split_bool_eqs d};
fun update_split_bool_eqs f (Data d) =
  Data{verbosity = #verbosity d, time = #time d, hammer_timeout = #hammer_timeout d,
    split_bool_eqs = f (#split_bool_eqs d)};

fun set_verbosity verbosity = update_verbosity (K verbosity);
fun set_hammer_timeout timeout = update_hammer_timeout (K timeout);
fun set_timing time = update_time (K time);
fun set_split_bool_eqs split = update_split_bool_eqs (K split);

val short_timeout = "10";
val med_timeout = "20";
val long_timeout = "30";

(* Dummy data *)
val empty = Data{verbosity = 0, time = false, hammer_timeout = short_timeout, split_bool_eqs = false};

(* val silent = empty;
val noisy = Data{verbosity = 100, hammer_timeout = 10}; (*FIXME*)
*)
structure Data = Theory_Data
  ( type T = T
    val empty = empty
    val extend = I
    val merge = fst)

(* val set_verbosity = Data.put *)

fun set_silent thy = Data.put (set_verbosity 0 (Data.get thy)) thy;
fun set_noisy thy = Data.put (set_verbosity 100 (Data.get thy)) thy;

fun set_hammer_timeout_short thy = Data.put (set_hammer_timeout short_timeout (Data.get thy)) thy;
fun set_hammer_timeout_medium thy = Data.put (set_hammer_timeout med_timeout (Data.get thy)) thy;
fun set_hammer_timeout_long thy = Data.put (set_hammer_timeout long_timeout (Data.get thy)) thy;

(*fun set_time thy = Data.put (set_time true (Data.get thy)) thy;*)
fun set_time thy = Data.put (set_timing true (Data.get thy)) thy;
fun set_no_time thy = Data.put (set_timing false (Data.get thy)) thy;

fun set_bool_eq_split thy = Data.put (set_split_bool_eqs true (Data.get thy)) thy;
fun set_no_bool_eq_split thy = Data.put (set_split_bool_eqs false (Data.get thy)) thy;


val verbosity = get_verbosity o Data.get o Proof_Context.theory_of
val sledgehammer_timeout = get_hammer_timeout o Data.get o Proof_Context.theory_of
val timing = get_timing o Data.get o Proof_Context.theory_of
val split_bool_eqs = get_split_bool_eqs o Data.get o Proof_Context.theory_of
end
