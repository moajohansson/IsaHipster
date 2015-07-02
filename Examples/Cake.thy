theory Cake
imports "$HIPSTER_HOME/IsaHipster"

begin

datatype Slice = Chocolate | Marzipan | Berries 

(* A "Swedish piece" is the last slice of cake that any Swedish person will
   feel greedy and impolite if taking. It will typically be cut smaller and smaller,
   as everybody desperately tries to avoid taking the very last tiny bit. *)
datatype Cake = Eaten | SwedishPiece Slice | BigPiece Slice Cake Slice

fun like :: "Slice \<Rightarrow> bool"
where
   "like Chocolate = False"
 | "like Marzipan = True"
 | "like Berries = True"
 
fun isTasty :: "Cake \<Rightarrow> bool"
where
    "isTasty Eaten = True"
  | "isTasty (SwedishPiece slice) = like slice"
  | "isTasty (BigPiece leftSlice cake rightSlice) = 
  (like leftSlice \<and> like rightSlice \<and> isTasty cake)"

fun merge :: "Cake \<Rightarrow> Cake \<Rightarrow> Cake"
where 
    "merge Eaten cake = cake"
  | "merge cake Eaten = cake"
  | "merge (SwedishPiece slice1) (SwedishPiece slice2) = 
      BigPiece slice1 Eaten slice2"
  | "merge (SwedishPiece slice) (BigPiece sl cake sr)= 
      BigPiece slice (merge (SwedishPiece sl) cake) sr"
  | "merge (BigPiece sl cake sr) (SwedishPiece slice) = 
      BigPiece sl (merge cake (SwedishPiece sr)) slice"
  | "merge (BigPiece sl1 cake1 sr1) (BigPiece sl2 cake2 sr2) = 
      BigPiece sl1 (merge cake1 (merge (SwedishPiece sr1) cake2)) sr2"

fun cutLeft :: "Cake \<Rightarrow> (Slice * Cake)"
where
   "cutLeft (SwedishPiece slice) = (slice, Eaten)"
  |"cutLeft (BigPiece l cake r) = (l, merge cake (SwedishPiece r))"

fun cutRight :: "Cake \<Rightarrow> (Slice * Cake)"
where
   "cutRight (SwedishPiece slice) = (slice, Eaten)"
  |"cutRight (BigPiece l cake r) = (r, merge (SwedishPiece l) cake)"

hipster cutLeft cutRight


hipster merge isTasty
(*
lemma lemma_a [thy_expl,simp]: "merge x2 Eaten = x2"
by (hipster_induct_simp_metis Cake.merge.simps Cake.isTasty.simps)

lemma lemma_aa [thy_expl]: "merge (merge x2 y2) z2 = merge x2 (merge y2 z2)"
by (hipster_induct_simp_metis Cake.merge.simps Cake.isTasty.simps)

lemma unknown [thy_expl]: "\<lbrakk>isTasty x \<and> isTasty y\<rbrakk> \<Longrightarrow> isTasty (merge x y) = isTasty (merge y x)"
apply (induct x)
apply simp
apply simp


lemma unknown2 [thy_expl]: "isTasty (merge x x) = isTasty x"
by simp
*)


end
