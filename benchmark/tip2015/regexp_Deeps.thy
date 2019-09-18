theory regexp_Deeps
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Aa = X | Y

datatype Rr
  = Nill | Eps | Atom "Aa" | Plus "Rr" "Rr" | Seq "Rr" "Rr" | Star "Rr"

fun seq :: "Rr => Rr => Rr" where
"seq x y =
   (case x of
       Nill => x
     | other =>
         (case y of
             Nill => y
           | other =>
               (case x of
                   Eps => y
                 | other =>
                     (case y of
                         Eps => x
                       | other => Seq x y
                       ))))"

fun plus :: "Rr => Rr => Rr" where
"plus x y =
   (case x of
       Nill => y
     | other =>
         (case y of
             Nill => x
           | other => Plus x y
         )
   )"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun eqA :: "Aa => Aa => bool" where
"eqA (X) y = False"
| "eqA (Y) (X) = False"
| "eqA (Y) (Y) = True"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun eps :: "Rr => bool" where
"eps x =
   (case x of
       Eps => True
     | Plus p q => or2 (eps p) (eps q)
     | Seq p2 q2 => and2 (eps p2) (eps q2)
     | Star y => True
     | other \<Rightarrow> False)"

fun deeps :: "Rr => Rr" where
"deeps (Nill) = Nill"
| "deeps (Eps) = Nill"
| "deeps (Atom a) = Atom a"
| "deeps (Plus p q) = Plus (deeps p) (deeps q)"
| "deeps (Seq p2 q2) =
     (if and2 (eps p2) (eps q2) then Plus (deeps p2) (deeps q2) else
        Seq p2 q2)"
| "deeps (Star p3) = deeps p3"

fun epsRr :: "Rr => Rr" where
"epsRr x = (if eps x then Eps else Nill)"

fun step :: "Rr => Aa => Rr" where
"step x y =
   (case x of
      Atom a => (if eqA a y then Eps else Nill)
     | Plus p q => plus (step p y) (step q y)
     | Seq p2 q2 =>
         plus (seq (step p2 y) q2) (seq (epsRr p2) (step q2 y))
     | Star p3 => seq (step p3 y) x
     | other => Nill)"

fun recognise :: "Rr => Aa list => bool" where
  "recognise x (Nil2) = eps x"
| "recognise x (Cons2 z xs) = recognise (step x z) xs"

(*hipster seq plus or2 eqA and2 eps deeps epsRr step recognise *)

(*hipster plus or2 eqA and2*)
lemma lemma_a [thy_expl]: "plus x1 Nill = x1"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_aa [thy_expl]: "eqA x2 Y = eqA x2 x2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ab [thy_expl]: "eqA x2 X = False"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ac [thy_expl]: "eqA Y x2 = eqA x2 x2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ad [thy_expl]: "Plus x1 (plus x1 x1) = plus x1 (Plus x1 x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ae [thy_expl]: "plus (Plus x1 x1) x1 = Plus (plus x1 x1) x1"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_af [thy_expl]: "and2 (eqA x2 y2) (eqA y2 z2) = and2 (eqA x2 y2) (eqA x2 z2)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ag [thy_expl]: "and2 (eqA x15 y15) (eqA z15 z15) = and2 (eqA x15 y15) (eqA x15 z15)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ah [thy_expl]: "and2 (eqA x16 y16) (eqA z16 y16) = and2 (eqA x16 z16) (eqA x16 y16)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ai [thy_expl]: "and2 (eqA x16 y16) (eqA z16 x16) = and2 (eqA z16 x16) (eqA z16 y16)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

setup\<open>Hip_Tac_Ops.set_metis_to @{context} 1000\<close>

lemma lemma_aj [thy_expl]: "and2 (eqA x16 y16) (eqA z16 z16) = and2 (eqA z16 x16) (eqA z16 y16)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

setup\<open>Hip_Tac_Ops.set_metis_to @{context} 400\<close>

lemma lemma_ak [thy_expl]: "and2 (eqA x2 x2) (eqA y2 z2) = and2 (eqA x2 y2) (eqA x2 z2)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_al [thy_expl]: "or2 (eqA x2 y2) False = eqA x2 y2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_am [thy_expl]: "or2 (eqA x2 y2) True = True"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_an [thy_expl]: "or2 (eqA x2 y2) (eqA x2 y2) = eqA x2 y2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ao [thy_expl]: "or2 (eqA x15 y15) (eqA x15 x15) = eqA x15 x15"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ap [thy_expl]: "or2 (eqA x16 y16) (eqA y16 y16) = eqA y16 y16"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_aq [thy_expl]: "and2 (eqA x2 y2) False = False"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ar [thy_expl]: "and2 (eqA x2 y2) True = eqA x2 y2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_as [thy_expl]: "and2 (eqA x2 y2) (eqA x2 y2) = eqA x2 y2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_at [thy_expl]: "or2 (eqA x2 x2) (eqA x2 y2) = eqA x2 x2"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_au [thy_expl]: "or2 (eqA x15 x15) (eqA y15 x15) = eqA x15 x15"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_av [thy_expl]: "or2 (eqA x16 x16) (eqA y16 y16) = or2 (eqA y16 y16) (eqA x16 x16)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_aw [thy_expl]: "Plus x1 (plus x1 Rr.Eps) = plus x1 (Plus x1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ay [thy_expl]: "plus (plus x1 x1) (Plus x1 x1) = Plus (plus x1 x1) (plus x1 x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_az [thy_expl]: "plus (Plus x1 x1) (plus x1 x1) = Plus (plus x1 x1) (plus x1 x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ba [thy_expl]: "plus (Plus Rr.Eps x1) x1 = Plus (plus Rr.Eps x1) x1"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bb [thy_expl]: "Plus (Seq x1 y1) (plus z1 Rr.Eps) = plus (Seq x1 y1) (plus z1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bc [thy_expl]: "Plus (Seq x1 y1) (plus Rr.Eps z1) = plus (Seq x1 y1) (plus Rr.Eps z1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bd [thy_expl]: "Plus (Plus x1 y1) (plus z1 Rr.Eps) = plus (Plus x1 y1) (plus z1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_be [thy_expl]: "Plus (Plus x1 y1) (plus Rr.Eps z1) = plus (Plus x1 y1) (plus Rr.Eps z1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bf [thy_expl]: "plus (plus x1 Rr.Eps) (Seq y1 z1) = Plus (plus x1 Rr.Eps) (Seq y1 z1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bg [thy_expl]: "plus (plus x1 Rr.Eps) (Plus y1 z1) = Plus (plus x1 Rr.Eps) (Plus y1 z1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bh [thy_expl]: "plus (plus Rr.Eps x1) (Seq y1 z1) = Plus (plus Rr.Eps x1) (Seq y1 z1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bi [thy_expl]: "plus (plus Rr.Eps x1) (Plus y1 z1) = Plus (plus Rr.Eps x1) (Plus y1 z1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_br [thy_expl]: "Plus (Star x1) (plus y1 Rr.Eps) = plus (Star x1) (plus y1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bs [thy_expl]: "Plus (Star x1) (plus Rr.Eps y1) = plus (Star x1) (plus Rr.Eps y1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bt [thy_expl]: "Plus (Atom x1) (plus y1 Rr.Eps) = plus (Atom x1) (plus y1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_bu [thy_expl]: "Plus (Atom x1) (plus Rr.Eps y1) = plus (Atom x1) (plus Rr.Eps y1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cd [thy_expl]: "plus (plus x1 Rr.Eps) (Star y1) = Plus (plus x1 Rr.Eps) (Star y1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ce [thy_expl]: "plus (plus x1 Rr.Eps) (Atom y1) = Plus (plus x1 Rr.Eps) (Atom y1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cl [thy_expl]: "plus (plus Rr.Eps x1) (Star y1) = Plus (plus Rr.Eps x1) (Star y1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cm [thy_expl]: "plus (plus Rr.Eps x1) (Atom y1) = Plus (plus Rr.Eps x1) (Atom y1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cp [thy_expl]: "Plus Rr.Eps (plus x1 Rr.Eps) = plus Rr.Eps (plus x1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cq [thy_expl]: "Plus Rr.Eps (plus Rr.Eps x1) = plus Rr.Eps (plus Rr.Eps x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cr [thy_expl]: "plus (plus x1 x1) (Plus x1 Rr.Eps) = Plus (plus x1 x1) (plus x1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_cy [thy_expl]: "plus (plus x1 Rr.Eps) Rr.Eps = Plus (plus x1 Rr.Eps) Rr.Eps"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_dd [thy_expl]: "plus (plus Rr.Eps x1) Rr.Eps =
Plus (plus Rr.Eps x1) Rr.Eps"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_de [thy_expl]: "plus (plus Rr.Eps x1) (Star x1) =
Plus (plus Rr.Eps x1) (Star x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_dh [thy_expl]: "plus (Plus Rr.Eps x1) (plus x1 x1) =
Plus (plus Rr.Eps x1) (plus x1 x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_eo [thy_expl]: "plus (plus x1 Rr.Eps) (plus x1 Rr.Eps) =
Plus (plus x1 Rr.Eps) (plus x1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_ep [thy_expl]: "plus (plus x1 Rr.Eps) (plus Rr.Eps x1) =
Plus (plus x1 Rr.Eps) (plus Rr.Eps x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_fc [thy_expl]: "plus (plus Rr.Eps x1) (plus x1 Rr.Eps) =
Plus (plus Rr.Eps x1) (plus x1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_fd [thy_expl]: "plus (plus Rr.Eps x1) (plus Rr.Eps x1) =
Plus (plus Rr.Eps x1) (plus Rr.Eps x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_go [thy_expl]: "plus (plus x1 Rr.Eps) (plus Rr.Eps Rr.Eps) =
Plus (plus x1 Rr.Eps) (plus Rr.Eps Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_gw [thy_expl]: "plus (plus Rr.Eps x1) (plus Rr.Eps Rr.Eps) =
Plus (plus Rr.Eps x1) (plus Rr.Eps Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_he [thy_expl]: "plus (plus Rr.Eps Rr.Eps) (plus x1 Rr.Eps) =
Plus (plus Rr.Eps Rr.Eps) (plus x1 Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_hf [thy_expl]: "plus (plus Rr.Eps Rr.Eps) (plus Rr.Eps x1) =
Plus (plus Rr.Eps Rr.Eps) (plus Rr.Eps x1)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_hu [thy_expl]: "and2 (eqA x16 y16) (eqA z16 y16) = and2 (eqA z16 x16) (eqA z16 y16)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma lemma_hv [thy_expl]: "or2 (eqA x16 x16) (eqA y16 z16) = or2 (eqA y16 z16) (eqA x16 x16)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma unknown [thy_expl]: "or2 (eqA x x) (or2 a b) = or2 (or2 a b) (eqA x x)"
oops

lemma unknown [thy_expl]: "or2 (eqA x x) (and2 a b) = or2 (and2 a b) (eqA x x)"
oops

lemma unknown [thy_expl]: "and2 (eqA x x) (or2 a b) = and2 (or2 a b) (eqA x x)"
oops

lemma unknown [thy_expl]: "and2 (eqA x x) (and2 a b) = and2 (and2 a b) (eqA x x)"
oops

lemma unknown [thy_expl]: "or2 (or2 a b) False = or2 a b"
oops

lemma unknown [thy_expl]: "or2 (or2 a b) True = True"
oops

lemma unknown [thy_expl]: "or2 (or2 a b) (or2 a b) = or2 a b"
oops

lemma unknown [thy_expl]: "or2 (or2 a b) (and2 a b) = or2 a b"
oops

lemma unknown [thy_expl]: "or2 (and2 a b) False = and2 a b"
oops

lemma unknown [thy_expl]: "or2 (and2 a b) True = True"
oops

lemma unknown [thy_expl]: "or2 (and2 a b) (or2 a b) = or2 a b"
oops

lemma unknown [thy_expl]: "or2 (and2 a b) (and2 a b) = and2 a b"
oops

lemma unknown [thy_expl]: "and2 (or2 a b) False = False"
oops

lemma unknown [thy_expl]: "and2 (or2 a b) True = or2 a b"
oops

lemma unknown [thy_expl]: "and2 (or2 a b) (or2 a b) = or2 a b"
oops

lemma unknown [thy_expl]: "and2 (or2 a b) (and2 a b) = and2 a b"
oops

lemma unknown [thy_expl]: "and2 (and2 a b) False = False"
oops

lemma unknown [thy_expl]: "and2 (and2 a b) True = and2 a b"
oops

lemma unknown [thy_expl]: "and2 (and2 a b) (or2 a b) = and2 a b"
oops

lemma unknown [thy_expl]: "and2 (and2 a b) (and2 a b) = and2 a b"
oops

lemma unknown [thy_expl]: "plus (plus x Rr.Eps) (plus y Rr.Eps) =
Plus (plus x Rr.Eps) (plus y Rr.Eps)"
oops

lemma unknown [thy_expl]: "plus (plus x Rr.Eps) (plus Rr.Eps y) =
Plus (plus x Rr.Eps) (plus Rr.Eps y)"
oops

lemma unknown [thy_expl]: "plus (plus Rr.Eps x) (plus y Rr.Eps) =
Plus (plus Rr.Eps x) (plus y Rr.Eps)"
oops

lemma unknown [thy_expl]: "plus (plus Rr.Eps x) (plus Rr.Eps y) =
Plus (plus Rr.Eps x) (plus Rr.Eps y)"
oops

lemma xa: "seq x Rr.Eps = x"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xb: "seq x Nill = Nill"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xc: "seq Rr.Eps x = x"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xd: "seq x (Plus x x) = seq x (plus x x)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xe: "seq (Plus x x) x = seq (plus x x) x"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xf: "seq x (Plus x Rr.Eps) = seq x (plus x Rr.Eps)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xg: "seq x (Plus Rr.Eps x) = seq x (plus Rr.Eps x)"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xh: "seq Rr.Eps (plus x x) = plus x x"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xi: "seq (plus x x) Rr.Eps = plus x x"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

lemma xj: "seq (plus x x) Nill = Nill"
by (hipster_induct_schemes plus.simps or2.simps eqA.simps and2.simps)

hipster seq plus

(*hipster step recognise*)

theorem x0 :
  "!! (p :: Rr) (s :: Aa list) .
     (recognise (Star p) s) = (recognise (Star (deeps p)) s)"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
