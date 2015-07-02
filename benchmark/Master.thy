theory Master
imports Main
        "$HIPSTER_HOME/IsaHipster"

begin

datatype Nat = Z | S Nat

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Tree = Leaf | Node "'a Tree" 'a "'a Tree"

datatype ('a, 'b) Pair2 = Pair2 'a 'b

fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
| "butlast (Cons2 y (Nil2)) = Nil2"
| "butlast (Cons2 y (Cons2 x2 x3)) = Cons2 y (butlast (Cons2 x2 x3))"

fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (Nil2) = butlast x"
| "butlastConcat x (Cons2 z x2) = append x (butlast (Cons2 z x2))"

fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
| "count x (Cons2 z ys) =
     (if equal2 x z then S (count x ys) else count x ys)"

fun delete :: "Nat => Nat list => Nat list" where
  "delete x (Nil2) = Nil2"
| "delete x (Cons2 z xs) =
     (if equal2 x z then delete x xs else Cons2 z (delete x xs))"

fun drop :: "Nat => 'a list => 'a list" where
"drop (Z) y = y"
| "drop (S z) (Nil2) = Nil2"
| "drop (S z) (Cons2 x2 x3) = drop z x3"

fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (Nil2) = Nil2"
| "dropWhile x (Cons2 z xs) =
     (if x z then dropWhile x xs else Cons2 z xs)"

fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
| "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter x (Nil2) = Nil2"
| "filter x (Cons2 z xs) =
     (if x z then Cons2 z (filter x xs) else filter x xs)"

fun ins :: "Nat => Nat list => Nat list" where
  "ins x (Nil2) = Cons2 x (Nil2)"
| "ins x (Cons2 z xs) =
     (if lt x z then Cons2 x (Cons2 z xs) else Cons2 z (ins x xs))"

fun ins1 :: "Nat => Nat list => Nat list" where
  "ins1 x (Nil2) = Cons2 x (Nil2)"
| "ins1 x (Cons2 z xs) =
     (if equal2 x z then Cons2 z xs else Cons2 z (ins1 x xs))"

fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
| "insert2 x (Cons2 z xs) =
     (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"

fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
| "insort x (Cons2 z xs) =
     (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"

fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (Nil2) y = Nil2"
| "intersect (Cons2 z xs) y =
     (if elem z y then Cons2 z (intersect xs y) else intersect xs y)"

fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
| "last (Cons2 y (Nil2)) = y"
| "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"

fun lastOfTwo :: "Nat list => Nat list => Nat" where
  "lastOfTwo x (Nil2) = last x"
| "lastOfTwo x (Cons2 z x2) = last (Cons2 z x2)"

fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
| "len (Cons2 y xs) = S (len xs)"

fun map2 :: "('a => 'b) => 'a list => 'b list" where
  "map2 x (Nil2) = Nil2"
| "map2 x (Cons2 z xs) = Cons2 (x z) (map2 x xs)"

fun null :: "'a list => bool" where
  "null (Nil2) = True"
| "null (Cons2 y z) = False"

fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
| "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"

fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
| "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"

fun qrevflat :: "('a list) list => 'a list => 'a list" where
  "qrevflat (Nil2) y = y"
| "qrevflat (Cons2 xs xss) y = qrevflat xss (append (rev xs) y)"

fun revflat :: "('a list) list => 'a list" where
  "revflat (Nil2) = Nil2"
| "revflat (Cons2 xs xss) = append (revflat xss) xs"

fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
| "rotate (S z) (Nil2) = Nil2"
| "rotate (S z) (Cons2 x2 x3) = rotate z (append x3 (Cons2 x2 (Nil2)))"

fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
| "sort (Cons2 y xs) = insort y (sort xs)"

fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
| "sorted (Cons2 y (Nil2)) = True"
| "sorted (Cons2 y (Cons2 y2 ys)) =
     (if le y y2 then sorted (Cons2 y2 ys) else False)"

fun subset :: "Nat list => Nat list => bool" where
  "subset (Nil2) y = True"
| "subset (Cons2 z xs) y =
     (if elem z y then subset xs y else False)"

fun take :: "Nat => 'a list => 'a list" where
"take (Z) y = Nil2"
| "take (S z) (Nil2) = Nil2"
| "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"

fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (Nil2) = Nil2"
| "takeWhile x (Cons2 z xs) =
     (if x z then Cons2 z (takeWhile x xs) else Nil2)"

fun union :: "Nat list => Nat list => Nat list" where
  "union (Nil2) y = y"
| "union (Cons2 z xs) y =
     (if elem z y then union xs y else Cons2 z (union xs y))"

fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
| "zip (Cons2 z x2) (Nil2) = Nil2"
| "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair2 z x3) (zip x2 x4)"

fun zipConcat :: "'a => 'a list => 'b list => (('a, 'b) Pair2) list" where
  "zipConcat x y (Nil2) = Nil2"
| "zipConcat x y (Cons2 y2 ys) = Cons2 (Pair2 x y2) (zip y ys)"





fun double :: "Nat => Nat" where
  "double (Z) = Z"
| "double (S y) = S (S (double y))"

fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"

fun even :: "Nat => bool" where
  "even (Z) = True"
| "even (S (Z)) = False"
| "even (S (S z)) = even z"

fun exp :: "Nat => Nat => Nat" where
  "exp x (Z) = S Z"
| "exp x (S n) = mult x (exp x n)"

fun fac :: "Nat => Nat" where
  "fac (Z) = S Z"
| "fac (S y) = mult (S y) (fac y)"
 
fun half :: "Nat => Nat" where
  "half (Z) = Z"
| "half (S (Z)) = Z"
| "half (S (S z)) = S (half z)"

fun le :: "Nat => Nat => bool" where
  "le Z     y      = True"
| "le y Z      = False"
| "le (S z) (S x2) = le z x2"

fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S x2) (S z) = lt x2 z"

fun max2 :: "Nat => Nat => Nat" where
  "max2 Z Z = Z"
| "max2 (Z) (S y) = S y"
| "max2 (S z) (Z) = S z"
| "max2 (S z) (S x2) = S (max2 z x2)"

fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
| "min2 (S z) (Z) = Z"
| "min2 (S z) (S y1) = S (min2 z y1)"

fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
| "minus (S z) (Z) = S z"
| "minus (S z) (S x2) = minus z x2"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"


fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
| "mult (S z) y = plus y (mult z y)"
 
fun mult2 :: "Nat => Nat => Nat => Nat" where
  "mult2 (Z) y z = z"
| "mult2 (S x2) y z = mult2 x2 y (plus y z)"

definition one :: "Nat" where
  "one = S Z"

fun qexp :: "Nat => Nat => Nat => Nat" where
  "qexp x (Z) z = z"
| "qexp x (S n) z = qexp x n (mult x z)"

fun qfac :: "Nat => Nat => Nat" where
  "qfac (Z) y = y"
| "qfac (S z) y = qfac z (mult (S z) y)"

fun unequal :: "Nat => Nat => bool" where
  "unequal x y = (\<not> (equal2 x y))"
 

fun height :: "'a Tree => Nat" where
  "height (Leaf) = Z"
| "height (Node l y r) = S (max2 (height l) (height r))"

fun mirror :: "'a Tree => 'a Tree" where
  "mirror (Leaf) = Leaf"
| "mirror (Node l y r) = Node (mirror r) y (mirror l)"


end

