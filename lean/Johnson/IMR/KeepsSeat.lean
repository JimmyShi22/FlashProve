-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/KeepsSeat.lean: a relation on the first chain's record that the lots' blocks keep is kept by
every block that the description of the kinds' blocks alone (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean:
onlineDescriptionFromPublicPart) lays in front of the blocks behind the last link: GENERAL IN THE RELATION AND IN THE SEAT.

A law ABOUT the harness's texts (beside it: Frames1.lean: guardMark, chainBy; FillCore.lean: fill,
chainC; LotCore.lean: Lot.blocks; Pure.lean: partsAt, onlineDescriptionAfterTests, onlineDescriptionFromPublicPart): it turns none of them.
  guardMark_decides, guardMark_whole, retype_whole: the two wrappers keep what the block keeps.
  fill_keeps: BlocksKeep R (Johnson/Goal/Meaning/KeepsDriver.lean) of the driver's record that fill
    makes.
  chainC_first: what chainC returns is the driver's chain at fill's record.
  chainBy_front, chainBy_noFront: every block of frontOf c is Decides R, and c.front = [], for the
    chain c that chainBy returns.
  LotsKeep R lots G: WHAT IS ASKED OF A SEAT's LOTS.
  partsAt_base, partsAt_frames, partsAt_roadW: so of the parts that partsAt makes.
  pureZ_front: onlineDescriptionFromPublicPart Z T = .ok F → F is fileDescBy … c, c.front = [], and every block of frontOf c
    is Decides R: its opening is Johnson/IMR/PureJoin.lean's pure_chain and base_made. LotsKeep IS
      ASKED AT
    THE BLANK LETTERS ALONE.
  chainC_last, chainBy_back, LotsAll, partsAt_baseAll, pureZ_flat: THE WHOLE CHAIN: for whoever pays
    every block of every lot UNDER ITS OWN TEST ON THE PLAN: every block of c.blocksInOrder that passes its
    test on the plan is Decides R.
OBJECT: ProofFile.onlineDescriptionFromPublicPart's value at any seat T. USER: SeatKeeps.lean (at the seat ProofFile.pureSeat Z).
-/
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S firstChain)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (guardMark fill chainC chainBy Frames Gather FrameRole Lot Ground)

variable {R : S → S → Prop}

theorem guardMark_decides {b : Block S ProofFile.Cl} (W : Decides R b) : Decides R (guardMark b) :=
  fun s rs gs s' h => by
  obtain ⟨t, e, h⟩ := Keeps.ebind_ok (x := b.decide s rs gs) h
  split at h
  · cases h
    exact W s rs gs _ e
  · cases h

theorem guardMark_whole {b : Block S ProofFile.Cl} (W : Whole R b) : Whole R (guardMark b) :=
  ⟨guardMark_decides W.1, W.2.1, W.2.2⟩

theorem retype_whole {T Cl Cl' : Type} {Q : T → T → Prop} {b : Block T Cl} (W : Whole Q b) :
    Whole Q (b.retype : Block T Cl') := ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

variable {Cl : Type}

/-- **The driver's record that fill makes.** -/
theorem fill_keeps {bs : List (Block S Cl)} {z : Block S Cl} {fr : Frames S Cl}
    (hb : ∀ b ∈ bs, b.place.link ≠ none → Whole R b)
    (hbat : ∀ a mk, fr.batch a = some mk → ∀ f, FnCl R f → Decides R (mk f))
    (hl : ∀ l, Fn R (fr.lay l)) (hc : ∀ l, Fn R (fr.clear l)) (hf : Decides R fr.first) :
    BlocksKeep R (fill bs z fr) where
  block a b ha h := by
    have h' : (bs.find? fun b => b.place == a) = some b := h
    have hp : (b.place == a) = true :=
      List.find?_some (p := fun x : Block S Cl => x.place == a) h'
    have e : b.place = a := eq_of_beq hp
    exact hb b (List.mem_of_find?_eq_some h') (e ▸ ha)
  batch a mk ha h f hf' := by
    have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
    cases hq : fr.batch a with
    | some m =>
      rw [hq] at h'
      have e : some m = some mk := h'
      cases e
      exact hbat a _ hq f hf'
    | none =>
      rw [hq] at h'
      have h'' : ((bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h'
      obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 h''
      have hp : (b.place == a) = true :=
        List.find?_some (p := fun x : Block S Cl => x.place == a) hb'
      have e : b.place = a := eq_of_beq hp
      exact (hb b (List.mem_of_find?_eq_some hb') (e ▸ ha)).1
  lay := hl
  clear := hc
  first := hf

theorem chainC_first {bs : List (Block S Cl)} {links : List First.ModelPart} {fr : Frames S Cl}
    {c : Chain S Cl} (h : chainC bs links fr = .ok c) :
    ∃ z several, firstChain (fill bs.dropLast z fr) links several = some c := by
  unfold chainC at h
  split at h
  · cases h
  · rename_i z _
    dsimp only at h
    split at h
    · cases h
    · rename_i c' hc'
      split at h
      · cases h
      · cases h
        exact ⟨z, _, hc'⟩

/-- **The first chain that chainBy makes: every block in front of the blocks behind the last
link.** -/
theorem chainBy_front (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    {base : List (Block S ProofFile.Cl)} {fr : List (FrameRole × Block S ProofFile.Cl)}
    {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl} (h : chainBy Z base fr road = .ok c)
    (hb : ∀ b ∈ base, b.place.link ≠ none → Whole R b) (hfr : ∀ x ∈ fr, Whole R x.2)
    (hbat : ∀ a mk, road.batch a = some mk → ∀ f, FnCl R f → Decides R (mk f)) :
    ∀ b ∈ frontOf c, Decides R b := by
  unfold chainBy at h
  obtain ⟨z, several, hc⟩ := chainC_first h
  refine firstChain_front hr ht (fill_keeps ?_ hbat ?_ ?_ ?_) hc
  · intro b hb' hl
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hb')
    split
    · rename_i x hx
      simp only [hx] at hl
      exact Keeps.andThen_whole R ht _ _ _ (hb b₀ h₀ hl)
        (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx)))
    · rename_i hx
      simp only [hx] at hl
      exact hb b₀ h₀ hl
  · intro l t s' k
    dsimp only at k
    split at k
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1 _ _ _ _ k
    · cases k
      exact hr _
  · intro l t s' k
    dsimp only at k
    split at k
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1 _ _ _ _ k
    · cases k
      exact hr _
  · dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1
    · exact fun s _ _ s' k => by cases k; exact hr _

theorem chainBy_noFront {Z : ProofFile.Pub} {base : List (Block S ProofFile.Cl)}
    {fr : List (FrameRole × Block S ProofFile.Cl)} {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl}
    (h : chainBy Z base fr road = .ok c) : c.front = [] := by
  unfold chainBy at h
  obtain ⟨z, several, hc⟩ := chainC_first h
  exact firstChain_noFront hc

theorem chainC_last {bs : List (Block S Cl)} {links : List First.ModelPart} {fr : Frames S Cl}
    {c : Chain S Cl} (h : chainC bs links fr = .ok c) :
    ∃ z several, bs.getLast? = some z ∧
      firstChain (fill bs.dropLast z fr) links several = some c := by
  unfold chainC at h
  split at h
  · cases h
  · rename_i z hz
    dsimp only at h
    split at h
    · cases h
    · rename_i c' hc'
      split at h
      · cases h
      · cases h
        exact ⟨z, _, hz, hc'⟩

/-- **The blocks behind the last link, and the seal**: for whoever pays every block of the list. -/
theorem chainBy_back (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    {base : List (Block S ProofFile.Cl)} {fr : List (FrameRole × Block S ProofFile.Cl)}
    {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl} (h : chainBy Z base fr road = .ok c)
    (hb : ∀ b ∈ base, b.planOk = true → Whole R b) (hfr : ∀ x ∈ fr, Whole R x.2) :
    ∀ b ∈ backOf c, b.planOk = true → Decides R b := by
  unfold chainBy at h
  obtain ⟨z, several, hz, hc⟩ := chainC_last h
  refine firstChain_back (fun a b _ e => ?_) ?_ hc
  · have e' := List.mem_of_find?_eq_some e
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast e')
    split
    · rename_i x hx
      intro hp
      exact (Keeps.andThen_whole R ht _ _ _ (hb b₀ h₀ (Bool.and_eq_true _ _ ▸ hp).1)
        (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx)))).1
    · exact fun hp => (hb b₀ h₀ hp).1
  · obtain ⟨b₀, h₀, e₀⟩ := List.mem_map.1 (List.mem_of_getLast? hz)
    show z.planOk = true → Decides R z
    rw [← e₀]
    split
    · rename_i x hx
      intro hp
      exact (Keeps.andThen_whole R ht _ _ _ (hb b₀ h₀ (Bool.and_eq_true _ _ ▸ hp).1)
        (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx)))).1
    · exact fun hp => (hb b₀ h₀ hp).1

/-! ## The seat -/

/-- **What is asked of a seat's lots**, at the letters G. -/
structure LotsKeep (R : S → S → Prop) (lots : List Lot) (G : Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G,
    (b.place.link ≠ none ∨ (b.place.kind == KindName.frame) = true) → Whole R b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)

variable {T : ProofFile.PureSeat} {B : ProofFile.PureBase}

theorem partsAt_roadW (K : LotsKeep R T.lots B.G₀) {a : Place}
    {mk : (S → Except String (List ProofFile.Cl × S)) → Block S ProofFile.Cl}
    (h : (ProofFile.partsAt T B).road.batch a = some mk) :
    ∀ f, FnCl R f → Whole R (mk f) := by
  intro f hf
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some h₀
  exact guardMark_whole (K.batch L (List.mem_of_mem_filter hL) a mk₀ e f hf)

theorem partsAt_frames (K : LotsKeep R T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) :
    ∀ x ∈ (ProofFile.partsAt T B).frames, Whole R x.2 := by
  intro x hx
  simp only [ProofFile.partsAt] at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  · obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    obtain ⟨k1, k2⟩ := hall y hy
    have W : Whole R b := K.blocks y.1 k1 b (k2 ▸ hb1) (Or.inr hb2)
    split at e
    · cases e
    · cases e
    · cases e
      exact guardMark_whole W

theorem partsAt_base (hr : ∀ s, R s s) (K : LotsKeep R T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) : ∀ b ∈ base, b.place.link ≠ none → Whole R b := by
  intro b hb hl
  unfold ProofFile.PureParts.base at h
  obtain ⟨x, hx, e⟩ := mem_of_mapM_ok _ _ _ h b hb
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact guardMark_whole (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL _
      (fun s y k => by cases k; exact hr s))
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    exact guardMark_whole (K.blocks z.1 k1 b₀ (k2 ▸ List.mem_of_find?_eq_some hb₀) (Or.inl hl))
  · split at e <;> cases e

theorem all_of_made (e : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) :
    ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀ := by
  intro x hx
  rw [e] at hx
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
  exact ⟨hL, rfl⟩

/-- **The description of the lots' blocks alone: every block in front of the blocks behind the last
link keeps what the lots' blocks keep.** -/
theorem pureZ_front (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    (K : ∀ G, ProofFile.blankBy T.links Z = some G → LotsKeep R T.lots G) {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides R b := by
  obtain ⟨B, base, c, A, B', hB, -, -, hbase, hc, -, -, e⟩ := IM.pure_chain h
  have hall := all_of_made (IM.base_made hB).2.2.2
  have K₀ := K _ (IM.base_made hB).2.2.1
  exact ⟨A, B', c, e, chainBy_noFront hc, chainBy_front hr ht hc
    (partsAt_base hr K₀ hall hbase) (partsAt_frames K₀ hall)
    (fun a mk e f hf => (partsAt_roadW K₀ e f hf).1)⟩

/-! ## The whole chain -/

/-- **What is asked of a seat's lots for the whole chain, beside LotsKeep**: every block THAT PASSES
ITS OWN TEST ON THE PLAN. -/
structure LotsAll (R : S → S → Prop) (lots : List Lot) (G : Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G, b.planOk = true → Whole R b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)

theorem partsAt_baseAll (hr : ∀ s, R s s) (K : LotsAll R T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) : ∀ b ∈ base, b.planOk = true → Whole R b := by
  intro b hb hp
  unfold ProofFile.PureParts.base at h
  obtain ⟨x, hx, e⟩ := mem_of_mapM_ok _ _ _ h b hb
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact guardMark_whole (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL _
      (fun s y k => by cases k; exact hr s))
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    exact guardMark_whole (K.blocks z.1 k1 b₀ (k2 ▸ List.mem_of_find?_eq_some hb₀) hp)
  · split at e <;> cases e

/-- **The description of the lots' blocks alone: every block of the first chain that passes its own
test on the plan keeps what the lots' blocks keep.** -/
theorem pureZ_flat (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    (K : ∀ G, LotsKeep R T.lots G) (Ka : ∀ G, LotsAll R T.lots G) {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides R b := by
  obtain ⟨B, base, c, A, B', hB, -, -, hbase, hc, -, -, e⟩ := IM.pure_chain h
  have hall := all_of_made (IM.base_made hB).2.2.2
  have hF := partsAt_frames (K _) hall
  refine ⟨A, B', c, e, fun b hb hp => ?_⟩
  rw [flat_eq (chainBy_noFront hc)] at hb
  rcases List.mem_append.1 hb with k | k
  · exact chainBy_front hr ht hc (partsAt_base hr (K _) hall hbase) hF
      (fun a mk e f hf => (partsAt_roadW (K _) e f hf).1) b k
  · exact chainBy_back ht hc (partsAt_baseAll hr (Ka _) hall hbase) hF b k hp

#print axioms chainBy_front
#print axioms partsAt_base
#print axioms pureZ_front
#print axioms pureZ_flat

end Meaning.K2
