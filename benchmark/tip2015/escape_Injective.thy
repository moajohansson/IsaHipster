theory escape_Injective
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Token = A | B | C | D | ESC | P | Q | R

fun isSpecial :: "Token => bool" where
"isSpecial ESC = True"
| "isSpecial P = True"
| "isSpecial Q = True"
| "isSpecial R = True"
| "isSpecial x = False"

fun code :: "Token => Token" where
"code ESC = ESC"
| "code P = A"
| "code Q = B"
| "code R = C"
| "code x = x"

fun escape :: "Token list => Token list" where
"escape (Nil2) = Nil2"
| "escape (Cons2 y xs) =
     (if isSpecial y then Cons2 ESC (Cons2 (code y) (escape xs)) else
        Cons2 y (escape xs))"

(*hipster isSpecial code escape *)

hipster isSpecial code escape
lemma lemma_a [thy_expl]: "code (code x1) = code x1"
by (hipster_induct_schemes isSpecial.simps code.simps escape.simps)

fun eqEsc :: "Token list => Token list \<Rightarrow> bool" where
"eqEsc xs ys = (xs = ys)"

hipster_cond isSpecial code  escape isSpecial

fun isNil :: "Token list \<Rightarrow> bool" where
"isNil Nil2 = True"
| "isNil _ = False"

hipster_cond isNil escape isSpecial
lemma lemma_aa [thy_expl]: "isNil (escape x5) = isNil x5"
by (hipster_induct_schemes isNil.simps escape.simps isSpecial.simps)

lemma lemma_ab [thy_expl]: "isNil x3 \<Longrightarrow> escape x3 = x3"
by (hipster_induct_schemes isNil.simps escape.simps isSpecial.simps)

lemma unknown [thy_expl]: "isNil y \<and> isNil x \<Longrightarrow> x = y"
by (hipster_induct_schemes isNil.simps escape.simps isSpecial.simps list.exhaust)

hipster_cond isSpecial isNil escape code isSpecial

theorem x0 :"
     ((escape xs) = (escape ys)) ==> (xs = ys)"
     (*apply(hipster_induct_schemes escape.simps isSpecial.simps code.simps Token.exhaust list.exhaust)*)

     apply(induction xs arbitrary: ys rule:escape.induct)
     apply(simp_all)
     apply(metis isNil.simps escape.simps thy_expl)
     apply(metis isNil.simps escape.simps escape.simps isSpecial.simps thy_expl)

     (*
     apply(metis thy_expl escape.simps isSpecial.simps code.simps list.exhaust Token.exhaust)*)
     (*apply(hipster_induct_schemes escape.simps isSpecial.simps code.simps Token.exhaust list.exhaust)*)
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
