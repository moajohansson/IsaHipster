theory prop_05
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin

(* XXX: for now changed order \<Longrightarrow> do something about those HO objects, such as f *)
theorem mapIntersperse: "intersperse (f a) (maps f xs) = maps f (intersperse a xs)"
by hipster_induct_schemes

end


