theory Naturals
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

ML {*

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (take n xs ~~ ys) end;
*}

datatype Nat = Z | S Nat
thm Nat.exhaust

fun leq :: "Nat => Nat => bool" where
  "leq Z _ = True"
| "leq _ Z = False"
| "leq (S x) (S y) = leq x y"

fun geq :: "Nat => Nat => bool" where
  "geq _ Z = True"
| "geq Z _ = False"
| "geq (S x) (S y) = geq x y"

fun add :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "add Z     n = n"
| "add (S n) m = S (add n m)"

fun sub :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "sub Z _     = Z"
| "sub (S n) Z = S n"
| "sub (S n) (S m) = sub n m"

(* we do all tail-recursion + call recursing on 1ast argument but
    should not be a need (?) *)
fun mul :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "mul Z     _ = Z"
| "mul (S n) m = add m (mul n m)"

fun exp :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "exp Z     _ = S Z"
| "exp (S n) m = mul m (exp n m)"

fun lt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "lt Z (S _) = True"
| "lt _ Z     = False"
| "lt (S n) (S m) = lt n m"

fun gt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "gt Z _ = False"
| "gt _ Z = True"
| "gt (S n) (S m) = gt n m"

fun eqN :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "eqN Z Z = True"
| "eqN (S n) (S m) = eqN n m"
| "eqN _     _     = False"

fun max :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "max Z n = n"
| "max m Z = m"
| "max (S n) (S m) = S (max n m)"

fun lez :: "Nat \<Rightarrow> bool" where
  "lez x = (x = Z)"
(* FIXME: primes ( ' ) are not liked... bash script errors... escape properly? *)
fun lezp :: "Nat \<Rightarrow> bool" where
  "lezp Z = True"
| "lezp _ = False"
fun lezpp :: "Nat \<Rightarrow> bool" where
  "lezpp x = eqN x Z"


end

