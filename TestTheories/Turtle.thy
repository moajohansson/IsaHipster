theory Turtle
imports Main
        "$HIPSTER_HOME/IsaHipster"

begin

type_synonym angle = int
type_synonym point = "int * int"
type_synonym distance = int

record turtle =     facing :: angle
                    loc :: point
                    fly :: bool

type_synonym instant = "((turtle * turtle) * string) list"
type_synonym transiton = "turtle \<Rightarrow> turtle option"

datatype prog = Empty "(prog list)" | Node transiton "(prog list)"

fun endPoint :: "point \<Rightarrow> angle \<Rightarrow> distance \<Rightarrow> point" where
  "endPoint (x, y) d l = (x + l * d, y + l * d)"

fun moveT :: "distance \<Rightarrow> turtle \<Rightarrow> turtle" where
  "moveT n t = t \<lparr> loc := endPoint (loc t) (facing t) n \<rparr>"

fun rotateT :: "angle \<Rightarrow> turtle \<Rightarrow> turtle" where
  "rotateT d t = t \<lparr> facing := (facing t + d) mod 6 \<rparr>"

definition initTurtle :: "turtle" where
  "initTurtle = \<lparr> facing = 0, loc = (0, 0), fly = False\<rparr>"

definition empty :: "prog" where
 "empty = Empty []"

fun K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "K b x = b"

definition die :: "prog" where
  "die = Node (K None) []"

fun transit :: "(turtle \<Rightarrow> turtle) \<Rightarrow> prog" where
  "transit f = Node (Some o f) []"

definition idle :: "prog" where
  "idle = transit id"

definition penup :: "prog" where
  "penup = transit (\<lambda> t. t \<lparr>fly := True\<rparr>)"

definition pendown :: "prog" where
  "pendown = transit (\<lambda> t. t \<lparr>fly := False\<rparr>)"

fun forward :: "distance \<Rightarrow> prog" where
  "forward n = transit (moveT n)"

fun backward :: "distance \<Rightarrow> prog" where
  "backward n = transit (moveT (- n))"

fun right :: "angle \<Rightarrow> prog" where
  "right d = transit (rotateT (- d))"

fun left :: "angle \<Rightarrow> prog" where
  "left d = transit (rotateT d)"

fun getCh :: "prog \<Rightarrow> prog list" where
  "getCh (Empty  cs) = cs"
| "getCh (Node _ cs) = cs"

fun getOp :: "prog \<Rightarrow> prog list \<Rightarrow> prog" where
  "getOp (Empty  _) = Empty"
| "getOp (Node t _) = Node t"

function inject :: "int \<Rightarrow> prog \<Rightarrow> (int \<Rightarrow> prog \<Rightarrow> bool) \<Rightarrow> (prog \<Rightarrow> prog \<Rightarrow> prog) \<Rightarrow> prog \<Rightarrow> prog" where
  "inject n new fcond gtrans p =
    (if fcond n p then gtrans new p
                  else getOp p (map (inject ((\<lambda>p . case p of Empty _ \<Rightarrow> n
                                                           | Node _ _ \<Rightarrow> n + 1) p) new fcond gtrans) (getCh p)))"
by auto

fun replace :: "int \<Rightarrow> prog \<Rightarrow> (int \<Rightarrow> prog \<Rightarrow> bool) \<Rightarrow> prog \<Rightarrow> prog" where
  "replace n new f = inject n new f (\<lambda>r _. r)"

fun append :: "int \<Rightarrow> prog \<Rightarrow> (int \<Rightarrow> prog \<Rightarrow> bool) \<Rightarrow> prog \<Rightarrow> prog" where
  "append n new f = inject n new f (\<lambda>r p. getOp p [r])"

fun isLeaf :: "prog \<Rightarrow> bool" where
  "isLeaf p = List.null (getCh p)"

fun isLastAction :: "prog \<Rightarrow> bool" where (* also possible via a definition, of course *)
  "isLastAction p = isLeaf p"

fun hasEmptyAction :: "prog \<Rightarrow> bool" where
  "hasEmptyAction (Empty _) = True"
| "hasEmptyAction _         = False"

fun isEmpty :: "prog \<Rightarrow> bool" where
  "isEmpty (Empty []) = True"
| "isEmpty (Empty cs) = list_all isEmpty cs"
| "isEmpty _          = False"

fun seq :: "prog \<Rightarrow> prog \<Rightarrow> prog" (infixr ">*>" 65) where
  "seq p q = append 0 q (\<lambda>_ x. isLeaf x) p"

fun par :: "prog \<Rightarrow> prog \<Rightarrow> prog" (infixr "<|>" 65) where
  "par p q = Empty [p, q]"

fun lifespan :: "int => prog => prog" where
  "lifespan n = replace 0 die (\<lambda>i _. i = n)"

fun limited :: "int => prog => prog" where
  "limited n = replace 0 (Empty []) (\<lambda>i _. i = n)"

fun times :: "int \<Rightarrow> prog \<Rightarrow> prog" where
  "times n p = (if n \<le> 0 then Empty [] else p >*> times (n - 1) p)"

function forever :: "prog \<Rightarrow> prog" where
  "forever p = p >*> forever p"
by auto

fun firstAction :: "prog \<Rightarrow> prog list \<Rightarrow> prog" where
  "firstAction p l = getOp p l"

fun restActions :: "prog \<Rightarrow> prog list" where
  "restActions p = getCh p"

lemma test: "(p <|> q) >*> r = (p >*> r) <|> (q >*> r)"
by hipster_induct_schemes

end

