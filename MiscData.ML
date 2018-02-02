(*  Author:     Johannes Åman Pohjola, Chalmers University of Technology

Miscellaneous configuration data 
*)

(*-----------------------------------------------------------------------------------------*)
(* Data about tactics for hard/routine reasoning used for theory exploration *)
(*-----------------------------------------------------------------------------------------*)

structure Misc_Data =
struct

datatype T = Data of
  { verbosity : int }


fun get_verbosity (Data d) = (#verbosity d)

(* Dummy data *)
val empty = Data{verbosity = 0};

val silent = empty;
val noisy = Data{verbosity = 100};

structure Data = Theory_Data
  ( type T = T
    val empty = empty
    val extend = I
    val merge = fst)

val set_verbosity = Data.put

val set_silent = set_verbosity silent
val set_noisy = set_verbosity noisy

val verbosity = get_verbosity o Data.get o Proof_Context.theory_of

end
