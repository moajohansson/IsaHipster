theory TestML
imports "$HIPSTER_HOME/IsaHipster"
begin

ML \<open>

val s = "((Suc Zero_nat) = one_nat)\n\n((plus_nat x Zero_nat) = x)"

val [c1,c2] = s
                        |> Library.trim_line
                       (* |> rename_to_Isabelle_consts *)
                        |> Library.split_lines
                        |> filter (fn x => not (x = ""));

Library.translate_string;
val mapaway = (fn x => if (x = "Zero_nat") then "0" else x);
val c1' = Library.space_explode " " c1;
val c3 = map mapaway c1';
Library.space_implode " " c1';

\<close>
end