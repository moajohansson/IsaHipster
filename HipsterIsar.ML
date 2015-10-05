(*  Author:     Moa Johansson, Chalmers University of Technology

Isar commands for Hipster theory exploration invocation.
*)


(* Install a Parser for HipSpec. It takes a list of constant names as input *)
let
fun call_hipster consts =   
  Local_Theory.target
    (fn ctxt => 
      let 
        fun get_const_name ctxt c = 
          c |> Proof_Context.read_const {proper=true, strict = false} ctxt (*false dummyT *)
            |> dest_Const
            |> fst
      in   
        consts 
          |> map (get_const_name ctxt)
          |> Hipster_Explore.explore ctxt
          |> fst
      end);
in
Outer_Syntax.local_theory @{command_keyword "hipster"} 
      "Theory Exploration with Hipster"
      (Scan.repeat1 Parse.const >> call_hipster)
end;

let
(* For now, assume predicate to be used as cond is first arg in list of consts *)
fun call_hipster consts =   
  Local_Theory.target
    (fn ctxt => 
      let 
        fun get_const_name ctxt c = 
          c |> Proof_Context.read_const {proper = true, strict = false} ctxt  (*false dummyT *)
            |> dest_Const
            |> fst 
        val const_nms = map (get_const_name ctxt) consts
                 
      in   
        fst (Hipster_Explore.explore_cond (SOME (hd const_nms)) ctxt const_nms)
      end);
in
Outer_Syntax.local_theory @{command_keyword "hipster_cond"} 
      "Theory Exploration for conditional lemmas with Hipster"
      (Scan.repeat1 Parse.const >> call_hipster)
end;


