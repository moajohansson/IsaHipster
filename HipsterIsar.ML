

(* Install a Parser for HipSpec. It takes a list of constant names as input *)
let
fun call_hipster consts =   
  Local_Theory.target 
  (fn ctxt => 
      let 
        fun get_const_name ctxt c = 
            c |> Proof_Context.read_const ctxt false dummyT
              |> dest_Const
              |> fst          
      in   
        consts 
          |> map (get_const_name ctxt)
          |> Hipster_Explore.explore ctxt
          |> fst
      end);
in
Outer_Syntax.local_theory @{command_spec "hipster"} 
      "Theory Exploration with Hipster"
      (Scan.repeat1 Parse.const >> call_hipster)
end;


