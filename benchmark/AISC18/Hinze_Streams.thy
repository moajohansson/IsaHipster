(* Attempting to discover laws form Hinze's stream calculus using Hipster *)
theory "Hinze_Streams"
  imports Main "$HIPSTER_HOME/IsaHipster"
    "~~/src/HOL/Library/BNF_Corec"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
setup Misc_Data.set_time

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

datatype ('a, 'b) Twople = Pair2 (fst2: 'a) (snd2: 'b)

primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"

(* Lifting *)
primcorec spure :: "'a \<Rightarrow> 'a Stream" where  
  "shd (spure x) = x"
| "stl (spure x) = spure x"

(* Sequential application *)
primcorec sapp :: " ('a \<Rightarrow> 'b) Stream \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "shd (sapp fs xs) = (shd fs) (shd xs)"
| "stl (sapp fs xs) = sapp (stl fs) (stl xs)"

primcorec szip :: "'a Stream \<Rightarrow> 'b Stream \<Rightarrow> (('a, 'b) Twople) Stream" where
  "shd (szip s1 s2) = Pair2 (shd s1) (shd s2)"
| "stl (szip s1 s2) = szip (stl s1) (stl s2)"

(* Map *)
primcorec smap2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap2 f xs = sapp (spure f) xs"

(* Interleaving *)
primcorec sinterleave :: "'a Stream \<Rightarrow> 'a Stream \<Rightarrow> 'a Stream" where
  "sinterleave s t = SCons (shd s) (sinterleave t (stl s))"

(* Tabulate and lookup *)
datatype MyNat = MyZero | MySuc MyNat

primcorec stabulate :: "(MyNat \<Rightarrow> 'a) \<Rightarrow> 'a Stream" where
  "stabulate f = SCons (f MyZero) (stabulate (f \<circ> (\<lambda>x. MySuc x)))"

fun slookup :: "'a Stream \<Rightarrow> (MyNat \<Rightarrow> 'a)" where
  "slookup s MyZero = shd s" |
  "slookup s (MySuc n) = slookup (stl s) n"

(* Pairs of streams *)
primcorec szip2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream \<Rightarrow> 'c Stream" where
  "szip2 g s t = sapp (sapp (spure g) s) t"

primcorec spair :: "'a Stream => 'b Stream => ('a, 'b) Twople Stream" where
  "spair xs ys = szip2 Pair2 xs ys"

(* Iterate *)
primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "siterate f a = SCons a (siterate f (f a))"

(* Recurse *)
primcorec monomap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Stream \<Rightarrow> 'a Stream" where
  "monomap f xs = SCons (f (shd xs)) (monomap f (stl xs))"

friend_of_corec monomap where
   "monomap f xs = SCons (f (shd xs)) (monomap f (stl xs))"
  by (auto intro: monomap.code)

corec srecurse :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "srecurse f a = SCons a (monomap f (srecurse f a))"

(* Unfolding *)
primcorec sunfold :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "sunfold g f a = SCons (g a) (sunfold g f (f a))"

(* Uncomment the following cohipster calls to explore this theory *)
(* cohipster sapp spure Fun.id Fun.comp *)
(* cohipster smap2 Fun.id Fun.comp *)
(* cohipster spair smap2 fst2 snd2 *)
(* cohipster sinterleave spure sapp *)
(* cohipster stabulate smap2 Fun.comp *)
(* cohipster slookup smap Fun.comp *)
(* cohipster siterate srecurse *)
(* cohipster sunfold Fun.comp smap *)
(* cohipster sunfold shd stl Fun.id *)

(* The output of the above cohipster calls follows below *)
(* lemma_a is Hinze's property 1, lemma_aa is Hinze's property 3 *)
(* cohipster sapp spure Fun.id Fun.comp *)
lemma lemma_a [thy_expl]: "sapp (spure id) y = y"
by(coinduction arbitrary: y rule: Stream.coinduct_strong)
  simp

lemma lemma_aa [thy_expl]: "sapp (spure z) (spure x2) = spure (z x2)"
by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  auto
  
lemma lemma_ab [thy_expl]: "SCons (y (shd z)) (stl z) = sapp (SCons y (spure id)) z"
by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
  (simp add: lemma_a)
  
lemma lemma_ac [thy_expl]: "SCons (z x2) (sapp (spure z) x3) = sapp (spure z) (SCons x2 x3)"
by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
  simp
  
lemma lemma_ad [thy_expl]: "sapp (SCons z (spure x2)) (spure x3) = SCons (z x3) (spure (x2 x3))"
by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
  (simp add: lemma_aa)
  
lemma lemma_ae [thy_expl]: "sapp (spure x2) (SCons z (spure x3)) = SCons (x2 z) (spure (x2 x3))"
by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
  (simp add: lemma_aa)
  
lemma lemma_af [thy_expl]: "sapp (spure x2) (sapp (spure x3) x4) = sapp (spure (x2 \<circ> x3)) x4"
by(coinduction arbitrary: x2 x3 x4 rule: Stream.coinduct_strong)
  auto
  
lemma lemma_ag [thy_expl]: "sapp (SCons y (spure id)) (spure z) = SCons (y z) (spure z)"
by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
  (metis lemma_ab spure.simps(1) spure.simps(2))
  
lemma lemma_ah [thy_expl]: "sapp (SCons id (spure y)) (spure z) = SCons z (spure (y z))"
by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
  (simp add: Hinze_Streams.lemma_aa)

(* cohipster smap2 Fun.id Fun.comp *)
(* lemma_ai is Hinze's property 5, lemma_aj is Hinze's property 6 *)
lemma lemma_ai [thy_expl]: "smap2 id y = y"
  by(coinduction arbitrary: y rule: Stream.coinduct_strong)
  (simp add: smap2.code)
  
lemma lemma_aj [thy_expl]: "smap2 z (spure x2) = spure (z x2)"
  by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  (simp add: lemma_aa)
  
lemma lemma_ak [thy_expl]: "stl (smap2 z x2) = smap2 z (stl x2)"
by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
simp

lemma lemma_al [thy_expl]: "smap2 (x2 \<circ> x3) x4 = smap2 x2 (smap2 x3 x4)"
by(coinduction arbitrary: x2 x3 x4 rule: Stream.coinduct_strong)
(simp add: lemma_af)

lemma lemma_am [thy_expl]: "SCons (z x2) (smap2 z x3) = smap2 z (SCons x2 x3)"
  by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
(simp add: smap2.code)

lemma lemma_an [thy_expl]: "SCons (shd z) (smap2 y (stl z)) = sapp (SCons id (spure y)) z"
  by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
    (simp add: smap2.code)

(* cohipster spair smap2 fst2 snd2 *)
(* None of these are among Hinze's properties *)
lemma lemma_ao [thy_expl]: "sapp (smap2 x2 x3) x4 = szip2 x2 x3 x4"
  by(coinduction arbitrary: x2 x3 x4 rule: Stream.coinduct_strong)
  simp
  
lemma lemma_ap [thy_expl]: "spair (stl z) (stl x2) = stl (spair z x2)"
  by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  simp
  
lemma lemma_aq [thy_expl]: "stl (spair z (spure x2)) = spair (stl z) (spure x2)"
by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  simp

lemma lemma_ar [thy_expl]: "stl (spair (spure z) x2) = spair (spure z) (stl x2)"
by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  simp
  
lemma lemma_as [thy_expl]: "stl (spair x2 (SCons z x3)) = spair (stl x2) x3"
by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
  simp
  
lemma lemma_at [thy_expl]: "stl (spair (SCons z x2) x3) = spair x2 (stl x3)"
by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
  simp
  
lemma lemma_au [thy_expl]: "spair (smap2 x2 (stl x3)) (stl x4) = stl (spair (smap2 x2 x3) x4)"
by(coinduction arbitrary: x2 x3 x4 rule: Stream.coinduct_strong)
  simp
  
lemma lemma_av [thy_expl]: "spair (stl x2) (smap2 x3 (stl x4)) = stl (spair x2 (smap2 x3 x4))"
by(coinduction arbitrary: x2 x3 x4 rule: Stream.coinduct_strong)
  simp
  
lemma unknown [thy_expl]: "spair (spure z) (spure x2) = spure (Pair2 z x2)"
oops
  
lemma unknown [thy_expl]: "spair (SCons z x3) (SCons x2 x4) = SCons (Pair2 z x2) (spair x3 x4)"
  oops

(* cohipster sinterleave spure sapp *)
(* lemma_ax is Hinze's property 10 *)
lemma lemma_aw [thy_expl]: "sinterleave (SCons y x2) z = SCons y (sinterleave z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.coinduct_strong)
  simp
  
lemma lemma_ax [thy_expl]: "sinterleave (spure y) (spure y) = spure y"
  by(coinduction arbitrary: y rule: Stream.coinduct_strong)
  auto

lemma lemma_ay [thy_expl]: "SCons y (sinterleave z (spure y)) = sinterleave (spure y) z"
  by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
simp

lemma lemma_az [thy_expl]: "sinterleave (spure z) (SCons y (spure z)) = SCons z (SCons y (spure z))"
  by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
    (simp add: lemma_aw lemma_ax)

(* cohipster stabulate smap2 Fun.comp *)
(* lemma_ba is Hinze's property 12 (commuted) *)
lemma lemma_ba [thy_expl]: "stabulate (z \<circ> x2) = smap2 z (stabulate x2)"
  by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
    (metis (no_types, lifting) comp_apply comp_assoc lemma_ak sapp.simps(1) smap2.code spure.simps(1) stabulate.simps(1) stabulate.simps(2))

(* cohipster slookup smap Fun.comp *)
(* lemma_bb is Hinze's property 13 (commuted) *)
lemma lemma_bb [thy_expl]: "slookup (smap z x2) x3 = z (slookup x2 x3)"
  apply (induct x3 arbitrary: x2)
  apply simp
  apply simp
  done
  
lemma lemma_bc [thy_expl]: "smap (x2 \<circ> x3) x4 = smap x2 (smap x3 x4)"
  by(coinduction arbitrary: x2 x3 x4 rule: Stream.coinduct_strong)
    auto
    
lemma lemma_bd [thy_expl]: "SCons (z x2) (smap z x3) = smap z (SCons x2 x3)"
by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
  simp

(* cohipster siterate srecurse *)
(* lemma_bg is Hinze's property 14 *)
lemma lemma_be [thy_expl]: "monomap y (siterate y z) = siterate y (y z)"
  by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
auto

lemma lemma_bf [thy_expl]: "monomap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
  by(coinduction rule: monomap.coinduct)
(simp add: lemma_be srecurse.cong_refl)

lemma lemma_bg [thy_expl]: "srecurse y z = siterate y z"
by(coinduction rule: srecurse.coinduct)
  (smt Stream.collapse Stream.inject lemma_be siterate.code srecurse.code srecurse.cong_base srecurse.cong_monomap)

(* cohipster sunfold Fun.comp smap *)
(* lemma_bi is Hinze's property 18 (commuted) *)
lemma lemma_bh [thy_expl]: "smap z (sunfold x2 x2 x3) = sunfold z x2 (x2 x3)"
  by(coinduction arbitrary: x2 x3 z rule: Stream.coinduct_strong)
    auto

lemma lemma_bi [thy_expl]: "sunfold (x2 \<circ> x3) x4 x5 = smap x2 (sunfold x3 x4 x5)"
  by(coinduction arbitrary: x2 x3 x4 x5 rule: Stream.coinduct_strong)
    auto

(* cohipster sunfold shd stl Fun.id *)
(* None of these are among Hinze's laws *)
lemma lemma_bj [thy_expl]: "sunfold id y (y z) = sunfold y y z"
by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
  auto

lemma lemma_bk [thy_expl]: "sunfold id id (z x2) = sunfold z id x2"
by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  auto
  
lemma lemma_bl [thy_expl]: "SCons z (sunfold y y z) = sunfold id y z"
by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
  (simp add: lemma_bj)
  
lemma lemma_bm [thy_expl]: "SCons (z x2) (sunfold z id x2) = sunfold z id x2"
by(coinduction arbitrary: x2 z rule: Stream.coinduct_strong)
  simp

end