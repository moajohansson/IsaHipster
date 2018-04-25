(*  Author:     Johannes Åman Pohjola, Chalmers University of Technology

Miscellaneous configuration data 
*)

(*-----------------------------------------------------------------------------------------*)
(* Data about tactics for hard/routine reasoning used for theory exploration *)
(*-----------------------------------------------------------------------------------------*)

structure Misc_Data =
struct

datatype T = Data of
  { verbosity : int, be_picky : bool }


fun get_verbosity (Data d) = (#verbosity d);
fun get_picky (Data d) = (#be_picky d);

fun update_verbosity f (Data d) =
  Data{verbosity = f (#verbosity d), be_picky = #be_picky d};
fun update_picky f (Data d) =
  Data{verbosity = #verbosity d, be_picky = f (#be_picky d)};

fun set_verbosity verbosity = update_verbosity (K verbosity);
fun set_picky picky = update_picky (K picky);

(* Dummy data *)
val empty = Data{verbosity = 0, be_picky = false};

(* val silent = empty;
val noisy = Data{verbosity = 100, be_picky = false}; (*FIXME*)
*)
structure Data = Theory_Data
  ( type T = T
    val empty = empty
    val extend = I
    val merge = fst)

(* val set_verbosity = Data.put *)

fun set_silent thy = Data.put (set_verbosity 0 (Data.get thy)) thy;
fun set_noisy thy = Data.put (set_verbosity 100 (Data.get thy)) thy;

fun set_nitpick thy = Data.put (set_picky true (Data.get thy)) thy;
fun set_no_nitpick thy = Data.put (set_picky false (Data.get thy)) thy; 

val verbosity = get_verbosity o Data.get o Proof_Context.theory_of
val nitpick = get_picky o Data.get o Proof_Context.theory_of
end
