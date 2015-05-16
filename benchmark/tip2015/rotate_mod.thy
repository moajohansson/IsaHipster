theory rotate_mod
imports Main
        "../../IsaHipster"
begin
  datatype Nat = S "Nat" | Z
  datatype 'a List2 = Cons2 "'a" "'a List2" | Nil2
  fun take :: "Nat => 'a List2 => 'a List2" where
  "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  | "take (S z) (Nil2) = Nil2"
  | "take (Z) y = Nil2"
  fun minus :: "Nat => Nat => Nat" where
  "minus (S z) (S x2) = minus z x2"
  | "minus (S z) (Z) = S z"
  | "minus (Z) y = Z"
  fun lt :: "Nat => Nat => bool" where
  "lt (S x2) (S z) = lt x2 z"
  | "lt (Z) (S z) = True"
  | "lt x (Z) = False"
  fun mod2 :: "Nat => Nat => Nat" where
  "mod2 x (S z) =
     (if lt x (S z) then x else mod2 (minus x (S z)) (S z))"
  | "mod2 x (Z) = Z"
  fun length :: "'a List2 => Nat" where
  "length (Cons2 y xs) = S (length xs)"
  | "length (Nil2) = Z"
  fun drop :: "Nat => 'a List2 => 'a List2" where
  "drop (S z) (Cons2 x2 x3) = drop z x3"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (Z) y = y"
  fun append :: "'a List2 => 'a List2 => 'a List2" where
  "append (Cons2 z xs) y = Cons2 z (append xs y)"
  | "append (Nil2) y = y"
  fun rotate :: "Nat => 'a List2 => 'a List2" where
  "rotate (S z) (Cons2 x2 x3) =
     rotate z (append x3 (Cons2 x2 (Nil2)))"
  | "rotate (S z) (Nil2) = Nil2"
  | "rotate (Z) y = y"
  (*hipster take minus lt mod2 length drop append rotate *)
  theorem x0 :
    "(rotate n xs) =
       (append
          (drop (mod2 n (length xs)) xs) (take (mod2 n (length xs)) xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
