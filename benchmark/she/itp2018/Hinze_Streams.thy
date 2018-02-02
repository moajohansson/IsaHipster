theory Hinze_Streams
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream" "types/Twople"
    Smap 
    Szip
    "~~/src/HOL/Library/BNF_Corec"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

(* Lifting *)
primcorec spure :: "'a \<Rightarrow> 'a Stream" where  
  "shd (spure x) = x"
| "stl (spure x) = spure x"

(* Sequential application *)
primcorec sapp :: " ('a \<Rightarrow> 'b) Stream \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "shd (sapp fs xs) = (shd fs) (shd xs)"
| "stl (sapp fs xs) = sapp (stl fs) (stl xs)"

(* Trying to discover idiom laws *)

(*cohipster sapp spure*)
(*Discovers nothing interesting*)
(*cohipster sapp spure Fun.id*)  
(*Discovers nothing interesting*)  
(*cohipster sapp spure Fun.comp*)  
(* crashes with following message:
Warning: generated term of untestable type Stream (X1 -> X2)
  3. sapp (spure f) z = sapp (spure f) z
  4. sapp (spure f) (spure y) = spure (f y)
tip-spec: src/QuickSpec/Eval.hs, line 361: Untestable instance spure (X1 . X2) of testable schema spure (X1 . X1)
*)
primcorec smap2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap2 f xs = sapp (spure f) xs"

(*cohipster smap2*)
(* ca 45 seconds *)
lemma lemma_ac [thy_expl]: "smap2 y (spure z) = spure (y z)"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    (metis sapp.simps(1) sapp.simps(2) smap2.code spure.simps(1) spure.simps(2))
    
lemma lemma_ad [thy_expl]: "stl (smap2 y z) = smap2 y (stl z)"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    simp
    
lemma lemma_ae [thy_expl]: "SCons (y z) (smap2 y x2) = smap2 y (SCons z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (metis Stream.sel(1) Stream.sel(2) lemma_ad sapp.simps(1) smap2.simps(1) spure.simps(1))
    
lemma lemma_af [thy_expl]: "smap2 z (SCons y (spure x2)) = SCons (z y) (spure (z x2))"
  by(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (metis lemma_ac lemma_ae)
    
lemma lemma_ag [thy_expl]: "sapp (SCons y (spure z)) (spure x2) = SCons (y x2) (spure (z x2))"
  by(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (metis Hinze_Streams.lemma_ac Stream.sel(1) Stream.sel(2) sapp.simps(1) sapp.simps(2) smap2.code spure.simps(1) spure.simps(2))


(* Trying to discover functor laws *)  
(*cohipster smap2 Fun.id*)
(*crashes with:
Warning: generated term of untestable type Stream (X1 -> X1)
  2. smap2 id2 x = x
tip-spec: src/QuickSpec/Eval.hs, line 361: Untestable instance spure id2 of testable schema spure id2*)
(*cohipster smap2 Fun.comp*)
(* crashes with Warning: generated term of untestable type Stream (X1 -> X2)
  1. smap2 (f . g) y = smap2 f (smap2 g y)
tip-spec: src/QuickSpec/Eval.hs, line 361: Untestable instance spure (X1 . X2) of testable schema spure (X1 . X1)
*)

(* Prove our definition of smap is equivalent to Hinze's *)
(*cohipster smap smap2*)
(* Discovered in ca 45 seconds *)
lemma lemma_ah [thy_expl]: "smap2 z x2 = smap z x2"
proof(coinduction arbitrary: x2 z rule: Stream.Stream.coinduct_strong)
  case Eq_Stream thus ?case
    using lemma_ad
    by (force simp add: lemma_ad)
qed
  
lemma lemma_ai [thy_expl]: "smap y (spure z) = spure (y z)"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto
    
lemma lemma_aj [thy_expl]: "smap z (SCons y (spure x2)) = SCons (z y) (spure (z x2))"
proof(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
  case Eq_Stream thus ?case
    using lemma_ai
    by (force simp add: lemma_ai)
qed

(* We have already discovered functor laws for the alternative def of smap, 
   see Smap.thy *)

primcorec szip2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream \<Rightarrow> 'c Stream" where
  "szip2 g s t = sapp (sapp (spure g) s) t"

primcorec spair :: "'a Stream => 'b Stream => ('a, 'b) Twople Stream" where
  "spair xs ys = szip2 Pair2 xs ys"
(*cohipster spair*)
(* This fails with "couls not deduce typeable", 
if we add typeable constraints to all function contexts
it takes 10 minutes and doesn't find anything very interesting,
we still can't find the properties we want for spair,
and all quickspec calls run much slower *)
(*cohipster spair smap fst2 snd2*)

(* Proof that our def of szip is equivalent to Hinze's *)
lemma "szip xs ys = spair xs ys"
  apply (coinduction arbitrary: xs ys rule: Stream.coinduct_strong)
  apply auto
  by (metis Stream.expand spair.code szip2.simps(1) szip2.simps(2))

(* trying to discover properties of lifted pairing *)
(*cohipster szip smap fst2 snd2*)
(* ca 45 seconds, discovers some trivial things but not what we were 
   looking for*)
primcorec sinterleave :: "'a Stream \<Rightarrow> 'a Stream \<Rightarrow> 'a Stream" where
  "sinterleave s t = SCons (shd s) (sinterleave t (stl s))"

(* trying to discover properties for interleave *)
(*cohipster sinterleave spure*)
(* ca 35 seconds *)
lemma lemma_ak [thy_expl]: "sinterleave (SCons y x2) z = SCons y (sinterleave z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    simp
    
(* Interleave 1 property *)    
lemma lemma_al [thy_expl]: "sinterleave (spure y) (spure y) = spure y"
  by(coinduction arbitrary: y rule: Stream.Stream.coinduct_strong)
    auto
    
lemma lemma_am [thy_expl]: "SCons y (sinterleave z (spure y)) = sinterleave (spure y) z"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    simp
    
lemma lemma_an [thy_expl]: "sinterleave (spure z) (SCons y (spure z)) = SCons z (SCons y (spure z))"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_ak lemma_al)

(*cohipster sinterleave sapp*)
(* Nothing interesting found *)
  
primcorec stabulate :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a Stream" where
  "stabulate f = SCons (f 0) (stabulate (f \<circ> (\<lambda>x. x + 1)))"
  
fun slookup :: "'a Stream \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "slookup s 0 = shd s" |
  "slookup s (Suc n) = slookup (stl s) n"

(*cohipster stabulate smap Fun.comp*)
(* ca 1 minute *)
  
(* Naturality of tabulate *)
lemma lemma_ao [thy_expl]: "stabulate (y \<circ> z) = smap y (stabulate z)"
proof(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
  case Eq_Stream thus ?case
    using stabulate.simps(1)
    by fastforce
qed

(* Trying to find naturality of lookup *)
(*cohipster slookup smap Fun.comp*)
(* Finds nothing interesting*)  

primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "siterate f a = SCons a (siterate f (f a))"
(*cohipster smap siterate*)
(* ca 30 seconds *)
(* map-iterate property *)  
lemma lemma_ap [thy_expl]: "smap y (siterate y z) = siterate y (y z)"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto
    
lemma lemma_aq [thy_expl]: "smap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
proof(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
  case Eq_Stream thus ?case
    using lemma_ap
    by (force simp add: lemma_ap)
qed
(* Searching for iterate fusion law *)
(*cohipster smap siterate Fun.comp*)
(* ca 45 seconds*)
  
(* Special case of fusion law *)  
lemma lemma_ar [thy_expl]: "smap z (siterate (y \<circ> z) x2) = siterate (z \<circ> y) (z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    auto

(*Our previous map function is not friendly so we use this one
  to define recurse *)
primcorec monomap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Stream \<Rightarrow> 'a Stream" where
  "monomap f xs = SCons (f (shd xs)) (monomap f (stl xs))"
friend_of_corec monomap where
   "monomap f xs = SCons (f (shd xs)) (monomap f (stl xs))"
  by (auto intro: monomap.code)

corec srecurse :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "srecurse f a = SCons a (monomap f (srecurse f a))"

(*cohipster srecurse*)
(* after ca 20 seconds
   proof loop crashes with "no matching coinduction rule found" when
   proving shd (srecurse y z) = z *) 
cohipster siterate srecurse
(* after ca 30 seconds
   proof loop crashes with "no matching coinduction rule found" when
   proving shd (srecurse y z) = z  
but srecurse f y = siterate f y is discovered *)
  

primcorec sunfold :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "sunfold g f a = SCons (g a) (sunfold g f (f a))"
  
(* Trying to find fusion law for unfold*)
(*cohipster sunfold Fun.comp*)
(* ca 20 seconds *)
(* Special case of fusion law *)
lemma lemma_as [thy_expl]: "sunfold (z \<circ> x2) x2 x3 = sunfold z x2 (x2 x3)"
  by(coinduction arbitrary: x2 x3 z rule: Stream.Stream.coinduct_strong)
    auto
(* Trying to find functor fusion for unfold*)
(*cohipster smap sunfold Fun.comp*)
(* ca 45 seconds *)
lemma lemma_at [thy_expl]: "smap y (sunfold z z x2) = sunfold y z (z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
  auto
(*Functor fusion*)  
lemma lemma_au [thy_expl]: "sunfold (y \<circ> z) x2 x3 = smap y (sunfold z x2 x3)"
  by(coinduction arbitrary: x2 x3 y z rule: Stream.Stream.coinduct_strong)
  auto

(* Trying to discover unfold reflection *)
cohipster sunfold shd stl Fun.id
lemma lemma_av [thy_expl]: "sunfold id y (y z) = sunfold y y z"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto
    
lemma lemma_aw [thy_expl]: "sunfold id id (y z) = sunfold y id z"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto
    
lemma lemma_ax [thy_expl]: "SCons z (sunfold y y z) = sunfold id y z"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_av)
    
lemma lemma_ay [thy_expl]: "SCons (y z) (sunfold y id z) = sunfold y id z"
  by(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    simp

end