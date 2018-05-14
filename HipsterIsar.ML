(*  Author:     Moa Johansson, Chalmers University of Technology

Isar commands for Hipster theory exploration invocation.
*)

(* Install a Parser for HipSpec. It takes a list of constant names as input *)

let
fun call_hipster consts =
    (fn ctxt =>
      let
        fun get_const_name ctxt c =
          c |> Proof_Context.read_const {proper=true, strict = false} ctxt (*false dummyT *)
            |> dest_Const
            |> fst
      in
        consts
          |> map (get_const_name ctxt)
          |> Hipster_Explore.explore ctxt;
        ctxt
      end);
in
Outer_Syntax.local_theory @{command_keyword "hipster"}
      "Theory Exploration with Hipster"
      (Scan.repeat1 Parse.const >> Hipster_Utils.maybe_time call_hipster)
end;
let
fun call_hipster consts =
    (fn ctxt =>
      let
        fun get_const_name ctxt c =
          c |> Proof_Context.read_const {proper=true, strict = false} ctxt (*false dummyT *)
            |> dest_Const
            |> fst
      in
        consts
          |> map (get_const_name ctxt)
          |> Hipster_Explore.explore_obs ctxt;
        ctxt
      end);
in
Outer_Syntax.local_theory @{command_keyword "cohipster"}
      "Theory Exploration with Hipster, using observers to explore codatatypes"
      (Scan.repeat1 Parse.const >> Hipster_Utils.maybe_time call_hipster)
end;

let
(* For now, assume predicate to be used as cond is first arg in list of consts *)
fun call_hipster consts =
    (fn ctxt =>
      let
        fun get_const_name ctxt c =
          c |> Proof_Context.read_const {proper = true, strict = false} ctxt  (*false dummyT *)
            |> dest_Const
            |> fst
        val const_nms = map (get_const_name ctxt) consts

      in
        Hipster_Explore.explore_cond (SOME (hd const_nms)) ctxt const_nms;
        ctxt
      end);
in
Outer_Syntax.local_theory @{command_keyword "hipster_cond"}
      "Theory Exploration for conditional lemmas with Hipster"
      (Scan.repeat1 Parse.const >> Hipster_Utils.maybe_time call_hipster)
end;

(*
(* Use simp and or sledgehammer, then prints out Isar snippet using standard Isabelle tactics. *)
method_setup hipster_induct = {*
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (Induct_CTac.hipster_induct ctxt)))
   *}
*)