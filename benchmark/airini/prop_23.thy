theory prop_23
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


datatype NPair = Pairn Nat Nat
datatype PList = PNil | PCons NPair PList
fun ptake :: "Nat => PList => PList" where
"ptake Z     xs           = PNil"
| "ptake (S _) PNil         = PNil"
| "ptake (S n) (PCons x xs) = PCons x (ptake n xs)"


  fun pzip :: "NL => NL => PList" where
  "pzip (Nil) y = PNil"
  | "pzip (Cons z x2) (Nil) = PNil"
  | "pzip (Cons z x2) (Cons x3 x4) = PCons (Pairn z x3) (pzip x2 x4)"

  fun pappend :: "PList => PList => PList" where
  "pappend (PNil) y = y"
  | "pappend (PCons z xs) y = PCons z (pappend xs y)"
  fun prev :: "PList => PList" where
  "prev (PNil) = PNil"
  | "prev (PCons y xs) = pappend (prev xs) (PCons y (PNil))"


theorem zipNotNil: "notNil rs \<Longrightarrow> pzip (Cons t ts) rs = PCons (Pairn t (head rs)) (pzip ts (tail rs))"
by hipster_induct_schemes


end



