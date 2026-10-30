-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/PileAt.lean: A SENTENCE ON THE PILE ALONG THE FIRST CHAIN, AT THE CHAIN's OWN lin. A copy of parts of
Johnson/LTPileR/PileSeat.lean, Johnson/IMR/SeatKeeps.lean and Johnson/IMR/OpenFlat.lean with one field narrowed: PileLaw.push is
asked at one shape lin₀, and the frames' lot is walked at Z.first alone. SeatKeeps.frames, asked at every first, is left idle by
okB := fun _ => False.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.LTPileR.PileSeat
import Johnson.IMR.OpenFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Door.PileAt

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub Cl)
open Meaning.K2
open Johnson.Desc.First.Walk

/-- **PileLaw with push asked at one shape.** -/
structure PileLawAt (lin₀ : Params.LinShape) (P : S → Prop) : Prop where
  same : ∀ s s', PileStays s s' → P s → P s'
  zero : ∀ (Q : LayPar) (fvs : List Bool) (kCol : Nat), Fn (Rides P) (openLayZero Q fvs kCol)
  push : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
    (lay : WsLay), Fn (Rides P) (clearWith X counts left
      fun masks w claims os => Pend.pendingRowO lay masks w claims lin₀ os)
  batch : ∀ p : K13.Where, Decides (Rides P) (K13.atM3 (Cl := Unit) p)

variable {lin₀ : Params.LinShape} {P : S → Prop}


theorem whole_ridesA (L : PileLawAt lin₀ P) {Cl : Type} {b : Block S Cl} (W : Whole PileStays b) :
    Whole (Rides P) b := whole_mono (fun s s' q => L.same s s' q) W

theorem fn_ridesA (L : PileLawAt lin₀ P) {f : S → Except String S} (h : Fn PileStays f) :
    Fn (Rides P) f := fun s t k => L.same s t (h s t k)

open Johnson.Desc.First.Walk.Seat in
/-- Every row of the links' frames. -/
theorem framesOf_ridesA (L : PileLawAt lin₀ P) {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (hl : first.lin = lin₀) (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (Rides P) f.lay ∧ Fn (Rides P) f.opened ∧ Fn (Rides P) f.clear := by
  subst hl
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_ridesA L (layFront_pile l), fun s t k I => by cases k; exact I, L.push _ _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_ridesA L (layFront_pile 0), L.zero _ _ _, L.push _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_ridesA L (layFront_pile l), fn_ridesA L (openAtt_pile _), L.push _ _ _ _⟩
      · cases e
        exact ⟨fn_ridesA L (layFront_pile l), fn_ridesA L (openLay_pile _), L.push _ _ _ _⟩

/-- **EVERY MAKER OF THE SEAT IN FRONT OF THE SUB-PROTOCOLS BEHIND THE LAST LINK.** -/
theorem seatKeeps_ridesA (L : PileLawAt lin₀ P) : SeatKeeps (Rides P) (fun _ => False) where
  refl := rides_refl
  trans := rides_trans
  frames := fun h _ => h.elim
  k1First := fun q gp _ => whole_ridesA L (firstAtS_pile q gp)
  k1Later := fun q gp l p m a _ => whole_ridesA L (laterAt_pile q gp l p m a)
  reads := fun h => whole_ridesA L (readsQuietAt_pile h)
  k3 := fun c r X cs' sh' a _ h => whole_ridesA L (theStated_pile c r X cs' sh' a h)
  k4 := fun p => whole_ridesA L (blockAtC_pile p)
  k5 := fun W l g bf _ h => whole_ridesA L (k5AtN_pile W l g bf h)
  k6 := fun h => whole_ridesA L (seatedClaims_pile h)
  k7 := fun W l => whole_ridesA L (k7Of_pile W l)
  k8 := fun p => whole_ridesA L (k8Whole_pile p)
  k11 := fun Q => whole_ridesA L (headMerge11_pile Q)
  closeOf := fun p Q b hb => whole_ridesA L (closeOf_pile p Q b hb)
  batch := fun p _ hf => batch_over rides_trans L.same p hf
  k2 := fun p _ => whole_ridesA L (k2_pile p)
  front := fun tl => fn_ridesA L (headFrontQ_pile tl)
  openQ := fun Q _ => fn_ridesA L (headOpenQ_pile Q)
  finFront := fn_ridesA L finishFrontQ_pile
  finBehind := fn_ridesA L finishBehindQ_pile

/-- **THE MAKERS BEHIND THE LAST LINK.** -/
theorem seatBack_ridesA (L : PileLawAt lin₀ P) : SeatBack (Rides P) where
  k12 := fun _ _ => whole_ridesA L (atFinish_pile _)
  k13M3 := fun p => ⟨L.batch p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p Q _ => whole_ridesA L (atM4_pile p Q)

theorem framesLot_keepsA (L : PileLawAt lin₀ P) (Z : Pub) (hl : Z.first.lin = lin₀)
    (G : Ground) : LotAll (Rides P) (ProofFile.framesLot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1L20.blocksOf Z := hb
  unfold P1L20.blocksOf at hb'
  split at hb'
  · rename_i fs hfs
    obtain ⟨f, hf, hb'⟩ := List.mem_flatMap.1 hb'
    obtain ⟨k1, k2, k3⟩ := framesOf_ridesA L hl hfs f hf
    unfold ProofFile.frameBlocks at hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact quiet_whole k1 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k2 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k3 (fun _ _ _ => rfl) rfl rfl
  · obtain rfl := List.mem_singleton.1 hb'
    exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl

theorem twelve_allA (L₀ : PileLawAt lin₀ P) (Z : Pub) (hl : Z.first.lin = lin₀)
    (h0 : Z.P.firstTree = 0) (G : Ground) :
    ∀ L ∈ [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
      ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, K13.lotEnd Z] ++ ProofFile.p4Pure Z, LotAll (Rides P) L G := by
  have H := seatKeeps_ridesA L₀
  intro L hL
  unfold ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact framesLot_keepsA L₀ Z hl G
  · exact k1Pure_keeps H Z h0 G
  · exact k2Pure_keeps H Z h0 G (fun _ _ _ => trivial)
  · exact k3Lot_keeps H Z G
  · exact k4Lot_keeps H Z G
  · exact k5LotN_keeps H Z G
  · exact k8Lot_keeps H Z G
  · exact k9Ninth_keeps H Z G
  · exact k11Lot_keeps H Z G
  · exact k13LotEnd_keeps H.refl Z G
  · exact k6Lot_keeps H Z G
  · exact lotAll_of (fun b hb => h1_whole H G b hb) (fun _ hb => nomatch hb)
      (fun _ _ h => nomatch h)

theorem thePure_keepsA (L₀ : PileLawAt lin₀ P) (Z : Pub) (hl : Z.first.lin = lin₀)
    (h0 : Z.P.firstTree = 0) (G : Ground) :
    LotsKeep (Rides P) (ProofFile.onlineFirstChainBlockTables Z) G := by
  have T := twelve_allA L₀ Z hl h0 G
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotKeeps (Rides P) L G := by
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact (T L (Or.inl (Or.inl h))).keep
    · exact (T L (Or.inl (Or.inr (Or.inl h)))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inl h))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))))))).keep
    · exact k12Lot_keeps Z G
    · exact k13Lot_keeps Z G
    · exact k13Lot4_keeps Z G
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h))))))))))).keep
    · exact (T L (Or.inr h)).keep
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2⟩

theorem thePure_allA (L₀ : PileLawAt lin₀ P) (Z : Pub) (hl : Z.first.lin = lin₀)
    (h0 : Z.P.firstTree = 0) (G : Ground) :
    LotsAll (Rides P) (ProofFile.onlineFirstChainBlockTables Z) G := by
  have Hb := seatBack_ridesA L₀
  have T := twelve_allA L₀ Z hl h0 G
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, (∀ b ∈ L.blocks G, b.planOk = true → Whole (Rides P) b) ∧
      ∀ a mk, L.batch G a = some mk → ∀ f, FnCl (Rides P) f → Whole (Rides P) (mk f) := by
    have up : ∀ {L : Lot}, LotAll (Rides P) L G → (∀ b ∈ L.blocks G, b.planOk = true → Whole (Rides P) b) ∧
        ∀ a mk, L.batch G a = some mk → ∀ f, FnCl (Rides P) f → Whole (Rides P) (mk f) :=
      fun K => ⟨fun b hb _ => K.1 b hb, K.2⟩
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact up <| T L (Or.inl (Or.inl h))
    · exact up <| T L (Or.inl (Or.inr (Or.inl h)))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))))))
    · exact k12Lot_if Hb Z G
    · exact up (k13Lot_all Hb Z G)
    · exact up (k13Lot4_all Hb Z h0 G)
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h))))))))))
    · exact up <| T L (Or.inr h)
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2⟩

/-- **open_flat at Rides P, with the narrowed law.** -/
theorem open_flatA {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (L₀ : PileLawAt lin₀ P) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hl : Z.first.lin = lin₀) : ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides (Rides P) b := by
  have hall := all_of_made (IM.base_made O.made).2.2.2
  have h0 := pub_firstTree (o := o) (pol := pol) (lay := lay) (KL := KL) O.pub
  have K₀ : LotsKeep (Rides P) (ProofFile.pureSeat o Z).lots Bs.G₀ := thePure_keepsA L₀ Z hl h0 Bs.G₀
  have Ka : LotsAll (Rides P) (ProofFile.pureSeat o Z).lots Bs.G₀ := thePure_allA L₀ Z hl h0 Bs.G₀
  have Fr : ∀ b ∈ frontOf c, Decides (Rides P) b :=
    chainBy_front rides_refl rides_trans O.chain
      (partsAt_base rides_refl K₀ hall O.places) (partsAt_frames K₀ hall)
      (fun a mk e f hf => (partsAt_roadW K₀ e f hf).1)
  intro b hb hp
  rw [flat_eq (chainBy_noFront O.chain)] at hb
  rcases List.mem_append.1 hb with k | k
  · exact Fr b k
  · exact chainBy_back rides_trans O.chain (partsAt_baseAll rides_refl Ka hall O.places)
      (partsAt_frames K₀ hall) b k hp

/-- **A sentence on the pile along any fold of the first chain, at the chain's own lin.** -/
theorem rides_fold {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (L₀ : PileLawAt lin₀ P) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hl : Z.first.lin = lin₀) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k ft : Nat) {s : S}
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) (hs : P s) : P r.1 :=
  Keeps.foldBlocks_keeps (Rides P) rides_refl rides_trans ft (c.blocksInOrder.take k)
    (fun b hb => open_flatA L₀ O hl b (List.mem_of_mem_take hb) (hp b (List.mem_of_mem_take hb)))
    s rs cols r h hs

end Johnson.AtFull.Shape.Door.PileAt

#print axioms Johnson.AtFull.Shape.Door.PileAt.rides_fold
