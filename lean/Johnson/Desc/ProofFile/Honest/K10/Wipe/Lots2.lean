-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Lots2.lean: the closing of a segment (K10): if each maker of the proof file's
seat has like outcomes at two states that are one under w, then so has each of the seat's lots, and so has every block
that the harness lays in front of the blocks behind the last link. General in w : S → S, S the first chain's state.
Three structures and three definitions of type Prop; the rest are theorems.

  face2, test_ok2      a gatherer that gathers nothing; a test that always passes
  fill_keeps2          BlocksKeep2 w (Wipe/Driver2.lean) of the driver's record that fill makes
  chainBy_front2       every block of Meaning.K2.frontOf c is Decides2 w, for the chain c that chainBy returns
  LotsKeep2 w lots G   what is asked of a seat's lots
  partsAt_roadW2, partsAt_each2, partsAt_tests2, partsAt_frames2, partsAt_base2   so of the parts that partsAt makes
  SeatKeeps2 w         what is asked of w: a field a maker, for the makers whose blocks stand inside a link
  SeatRest2 w          three texts that stand behind the last link and are asked all the same
  failed_of, reply_of, sameReply2   what the two guards read is one at like states
  LotKeeps2, LotAll2, lot_of2, lotAll_of2   what is asked of one lot; from its own blocks and its blocks with runs
  one theorem a lot    framesLot, k1Pure, k2Pure, k3Lot, k4Lot, k5LotN, k8Lot, k11Lot, k6Lot, k9Ninth, h1, k12Lot,
                       k13Lot, k13Lot4, k13LotEnd, each with the ending _keeps2 or _whole2
  thePure_keeps2       LotsKeep2 w (ProofFile.onlineFirstChainBlockTables Z) G

What is proved, by what. It follows Johnson/IMR/KeepsSeat.lean and Johnson/IMR/SeatKeeps.lean, lemma for lemma, over
Wipe/Alike.lean, Wipe/Wrap2.lean and Wipe/Driver2.lean. Where it is no copy: the lots' fields each and tests are asked;
the guard on the mark and the guard on the reply want that w leaves the mark and the reply; kind K3's field is asked at
the lot's own readers; the seal wants that w leaves what it asks. The premises of the one-state walk on the links built,
on the head's letters and on the number of the first tree are not needed and are gone.

Limits. SeatKeeps2 and SeatRest2 are shown of no w here. The lots of K12, of K13's batching and of W's sending stand
behind the last link and are of a kind: nothing is asked of them and nothing is shown. The finish's place and the seal
stand behind the last link too, yet SeatRest2 asks them: the lot of K2 picks the finish's block by the first letter of a
step's name, and the harness drops the seal by its role in the shape, so neither is told off by its place. No property
of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Driver2
import Johnson.IMR.SeatKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First

variable {w : S → S}

/-! ## 1 The harness -/

/-- A gatherer that gathers nothing hands back like states. -/
theorem face2 {Cl : Type} :
    FnCl2 w fun s => (Except.ok (([] : List Cl), s) : Except String (List Cl × S)) := by
  intro s s' hw
  refine AlikeE.ok ?_
  show (([] : List Cl), w s) = (([] : List Cl), w s')
  rw [hw]

/-- A test that always passes has one outcome. -/
theorem test_ok2 : Test2 w fun _ => (Except.ok () : Except String Unit) := fun _ _ _ => AlikeE.rfl'

section harness
variable {Cl : Type}

/-- **The driver's record that fill makes.** -/
theorem fill_keeps2 {bs : List (Block S Cl)} {z : Block S Cl} {fr : ProofFile.Frames S Cl}
    (hb : ∀ b ∈ bs, b.place.link ≠ none → Whole2 w b)
    (hbat : ∀ a mk, fr.batch a = some mk → ∀ f, FnCl2 w f → Decides2 w (mk f))
    (hl : ∀ l, Fn2 w (fr.lay l)) (hc : ∀ l, Fn2 w (fr.clear l)) (hf : Decides2 w fr.first)
    (he : ∀ l o cl, Test2 w (fr.each l o cl)) (ht : ∀ l, Test2 w (fr.tests l))
    (hs : ∀ t t' s s', w t = w t' → w s = w s' → fr.same t s = fr.same t' s') :
    BlocksKeep2 w (ProofFile.fill bs z fr) where
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
  each := he
  tests := ht
  same := hs

end harness

/-- **The first chain that chainBy makes: every block in front of the blocks behind the last link.** -/
theorem chainBy_front2 {Z : ProofFile.Pub} {base : List (Block S ProofFile.Cl)}
    {fr : List (ProofFile.FrameRole × Block S ProofFile.Cl)} {road : ProofFile.Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl}
    (h : ProofFile.chainBy Z base fr road = .ok c)
    (hb : ∀ b ∈ base, b.place.link ≠ none → Whole2 w b) (hfr : ∀ x ∈ fr, Whole2 w x.2)
    (hbat : ∀ a mk, road.batch a = some mk → ∀ f, FnCl2 w f → Decides2 w (mk f))
    (he : ∀ l o cl, Test2 w (road.each l o cl)) (ht : ∀ l, Test2 w (road.tests l))
    (hs : ∀ t t' s s', w t = w t' → w s = w s' → road.same t s = road.same t' s') :
    ∀ b ∈ Meaning.K2.frontOf c, Decides2 w b := by
  unfold ProofFile.chainBy at h
  obtain ⟨z, several, hc⟩ := Meaning.K2.chainC_first h
  refine firstChain_front2 (fill_keeps2 ?_ hbat ?_ ?_ ?_ he ht hs) hc
  · intro b hb' hl
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hb')
    split
    · rename_i x hx
      simp only [hx] at hl
      exact andThen_whole2 _ _ _ (hb b₀ h₀ hl)
        (guarded_whole2 _ _ hs (hfr x (List.mem_of_find?_eq_some hx)))
    · rename_i hx
      simp only [hx] at hl
      exact hb b₀ h₀ hl
  · intro l s s' hw
    dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1 s s' [] [] [] hw SameG.rfl'
    · exact AlikeE.ok hw
  · intro l s s' hw
    dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1 s s' [] [] [] hw SameG.rfl'
    · exact AlikeE.ok hw
  · dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1
    · exact fun _ _ _ _ _ hw _ => AlikeE.ok hw

/-! ## 2 The seat's lots -/

/-- **What is asked of a seat's lots**, at the letters G. -/
structure LotsKeep2 (w : S → S) (lots : List ProofFile.Lot) (G : ProofFile.Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G,
    (b.place.link ≠ none ∨ (b.place.kind == KindName.frame) = true) → Whole2 w b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl2 w f → Whole2 w (mk f)
  /-- the lot's Link.each -/
  each : ∀ L ∈ lots, ∀ l e, L.each G l = some e → ∀ o cl, Test2 w (e o cl)
  /-- the lot's Link.tests -/
  tests : ∀ L ∈ lots, ∀ l t, L.tests G l = some t → Test2 w t

/-- A link's test behind each run of claims has one outcome at like states. -/
def Each2 (w : S → S) (e : Nat × String → List ProofFile.Cl → S → Except String Unit) : Prop :=
  ∀ o cl, Test2 w (e o cl)

section parts
variable {T : ProofFile.PureSeat} {B : ProofFile.PureBase}

/-- The batching that the road hands the driver. -/
theorem partsAt_roadW2 (hm : ∀ s s', w s = w s' → s.failed = s'.failed) (K : LotsKeep2 w T.lots B.G₀)
    {a : Place} {mk : (S → Except String (List ProofFile.Cl × S)) → Block S ProofFile.Cl}
    (h : (ProofFile.partsAt T B).road.batch a = some mk) : ∀ f, FnCl2 w f → Whole2 w (mk f) := by
  intro f hf
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some h₀
  exact guardMark_whole2 hm (K.batch L (List.mem_of_mem_filter hL) a mk₀ e f hf)

/-- The test behind each run that the road hands the driver. -/
theorem partsAt_each2 (K : LotsKeep2 w T.lots B.G₀) (l : Nat) :
    Each2 w ((ProofFile.partsAt T B).road.each l) := by
  simp only [ProofFile.partsAt]
  split
  · rename_i f hf
    obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some hf
    exact K.each L (List.mem_of_mem_filter hL) l f e
  · exact fun _ _ => test_ok2

/-- The tests behind the adding that the road hands the driver. -/
theorem partsAt_tests2 (K : LotsKeep2 w T.lots B.G₀) (l : Nat) :
    Test2 w ((ProofFile.partsAt T B).road.tests l) := by
  simp only [ProofFile.partsAt]
  split
  · rename_i f hf
    obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some hf
    exact K.tests L (List.mem_of_mem_filter hL) l f e
  · exact test_ok2

/-- The blocks of the kind frame, with their roles. -/
theorem partsAt_frames2 (hm : ∀ s s', w s = w s' → s.failed = s'.failed) (K : LotsKeep2 w T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) :
    ∀ x ∈ (ProofFile.partsAt T B).frames, Whole2 w x.2 := by
  intro x hx
  simp only [ProofFile.partsAt] at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  · obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    obtain ⟨k1, k2⟩ := hall y hy
    have W : Whole2 w b := K.blocks y.1 k1 b (k2 ▸ hb1) (Or.inr hb2)
    split at e
    · cases e
    · cases e
    · cases e
      exact guardMark_whole2 hm W

/-- The blocks at the places inside a link. -/
theorem partsAt_base2 (hm : ∀ s s', w s = w s' → s.failed = s'.failed) (K : LotsKeep2 w T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) : ∀ b ∈ base, b.place.link ≠ none → Whole2 w b := by
  intro b hb hl
  unfold ProofFile.PureParts.base at h
  obtain ⟨x, hx, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h b hb
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact guardMark_whole2 hm (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL _ face2)
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    exact guardMark_whole2 hm (K.blocks z.1 k1 b₀ (k2 ▸ List.mem_of_find?_eq_some hb₀) (Or.inl hl))
  · split at e <;> cases e

end parts

/-! ## 3 What is asked of w -/

open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame) in
/-- **What is asked of a wiping w of the first chain's state**: a field a maker, for the makers whose blocks the
description lays inside a link. -/
structure SeatKeeps2 (w : S → S) : Prop where
  /-- what the guard on the mark reads -/
  failed : ∀ s, (w s).failed = s.failed
  /-- what the guard on the reply reads -/
  reply : ∀ s, (w s).out.reply = s.out.reply
  frames : ∀ {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public} {fs : List LinkFrame},
    framesOf built first W = .ok fs → ∀ f ∈ fs, Fn2 w f.lay ∧ Fn2 w f.opened ∧ Fn2 w f.clear
  k1First : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar),
    Whole2 w (VerifiableInference.Desc.K1.firstSegmentOpening (Cl := Unit) q gp)
  k1Later : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)),
    Whole2 w (VerifiableInference.Desc.K1.laterAt (Cl := Unit) q gp link piece moment arrays)
  reads : ∀ {G : ProofFile.Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit},
    ProofFile.readsQuietAt G l X piece = some b → Whole2 w b
  /-- at the lot's own readers (K3Lot.readersAt), not at every readers -/
  k3 : ∀ (Z : ProofFile.Pub), ∀ b ∈ K3Lot.hear Z, Whole2 w b
  k4 : ∀ p : OnBytes.Desc.First.K4.Par, Whole2 w (OnBytes.Desc.First.K4.blockAtC p)
  k5 : ∀ (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim},
    VerifiableInference.Desc.First.Att.P.k5AtN W l g before = some b → Whole2 w b
  k6 : ∀ {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim},
    VerifiableInference.Desc.Kinds.Head.seatedClaims W l before = some b → Whole2 w b
  k7 : ∀ (W : Verify.Public) (l : Nat), Whole2 w (VerifiableInference.Desc.Kinds.Reply.blockOf W l)
  k8 : ∀ p : VerifiableInference.Desc.First.K8.ParW, Whole2 w (VerifiableInference.Desc.First.K8.whole p)
  k11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP, Whole2 w (Johnson.Desc.First.ForkMerge.headClaimMergeKind P)
  closeOf : ∀ (p : VerifiableInference.Desc.K9.Where) (P : VerifiableInference.Desc.First.Close.Par),
    ∀ b ∈ VerifiableInference.Desc.K9.closeOf (Cl := Unit) p P, Whole2 w b
  batch : ∀ (p : VerifiableInference.Desc.K9.Where) {claims : S → Except String (List Claim × S)},
    FnCl2 w claims → Whole2 w (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p claims)
  /-- Link.each: the library's walk for a relation on one state does not ask it -/
  each : ∀ (k : VerifiableInference.Desc.K9.SegSort) (o : Nat × String) (cl : List Claim),
    Test2 w (VerifiableInference.Desc.K9.eachAtS k o cl)
  /-- Link.tests: the library's walk for a relation on one state does not ask it -/
  tests : ∀ (Z : ProofFile.Pub) (l : Nat) (t : S → Except String Unit), ProofFile.k9Tests Z l = some t → Test2 w t
  k2 : ∀ p : VerifiableInference.Desc.First.K2.P2, Whole2 w (VerifiableInference.Desc.First.K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn2 w (VerifiableInference.Desc.First.K2.headFrontQ tl)
  openQ : ∀ P : VerifiableInference.Desc.First.K2.HeadPar, Fn2 w (VerifiableInference.Desc.First.K2.headOpenQ P)

/-- **Three texts that stand behind the last link**, and which the walk asks all the same, because the harness's text
does not tell their places from a link's: the finish's two quiet steps, and what the seal asks. -/
structure SeatRest2 (w : S → S) : Prop where
  finFront : Fn2 w VerifiableInference.Desc.First.K2.finishFrontQ
  finBehind : Fn2 w VerifiableInference.Desc.First.K2.finishBehindQ
  sealAsks : ∀ s, VerifiableInference.Desc.First.endAsks (w s) = VerifiableInference.Desc.First.endAsks s

/-- The mark of failure is one at like states. -/
theorem failed_of (H : SeatKeeps2 w) : ∀ s s', w s = w s' → s.failed = s'.failed := fun s s' h =>
  (H.failed s).symm.trans ((congrArg (fun z : S => z.failed) h).trans (H.failed s'))

/-- The reply is one at like states. -/
theorem reply_of (H : SeatKeeps2 w) {s s' : S} (h : w s = w s') : s.out.reply = s'.out.reply :=
  (H.reply s).symm.trans ((congrArg (fun z : S => z.out.reply) h).trans (H.reply s'))

/-- The question of the guard on the reply has one answer at like states. -/
theorem sameReply2 (H : SeatKeeps2 w) :
    ∀ t t' s s', w t = w t' → w s = w s' → ProofFile.sameReply t s = ProofFile.sameReply t' s' := by
  intro t t' s s' ht hs
  unfold ProofFile.sameReply
  rw [reply_of H ht, reply_of H hs]

/-! ## 4 One lot -/

/-- What is asked of one lot: its blocks inside a link or of no kind, its batching, its two tests. -/
def LotKeeps2 (w : S → S) (L : ProofFile.Lot) (G : ProofFile.Ground) : Prop :=
  (∀ b ∈ L.blocks G, Meaning.K2.Asked b → Whole2 w b) ∧
    (∀ a mk, L.batch G a = some mk → ∀ f, FnCl2 w f → Whole2 w (mk f)) ∧
    (∀ l e, L.each G l = some e → ∀ o cl, Test2 w (e o cl)) ∧ ∀ l t, L.tests G l = some t → Test2 w t

/-- One lot, from its own blocks and its blocks with runs. -/
theorem lot_of2 {L : ProofFile.Lot} {G : ProofFile.Ground} (h1 : ∀ b ∈ L.own G, Meaning.K2.Asked b → Whole2 w b)
    (h2 : ∀ b ∈ L.hearC G, Meaning.K2.Asked b → Whole2 w b)
    (h3 : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl2 w f → Whole2 w (mk f))
    (h4 : ∀ l e, L.each G l = some e → ∀ o cl, Test2 w (e o cl))
    (h5 : ∀ l t, L.tests G l = some t → Test2 w t) : LotKeeps2 w L G := by
  refine ⟨fun b hb ha => ?_, h3, h4, h5⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact retype_whole2 (h1 b₀ h₀ ha)
  · exact h2 b hb ha

/-- The same of every block of the lot. -/
def LotAll2 (w : S → S) (L : ProofFile.Lot) (G : ProofFile.Ground) : Prop :=
  (∀ b ∈ L.blocks G, Whole2 w b) ∧
    (∀ a mk, L.batch G a = some mk → ∀ f, FnCl2 w f → Whole2 w (mk f)) ∧
    (∀ l e, L.each G l = some e → ∀ o cl, Test2 w (e o cl)) ∧ ∀ l t, L.tests G l = some t → Test2 w t

/-- Who pays every block pays those that are asked. -/
theorem LotAll2.keep {L : ProofFile.Lot} {G : ProofFile.Ground} (K : LotAll2 w L G) : LotKeeps2 w L G :=
  ⟨fun b hb _ => K.1 b hb, K.2⟩

/-- Every block of one lot, from its own blocks and its blocks with runs. -/
theorem lotAll_of2 {L : ProofFile.Lot} {G : ProofFile.Ground} (h1 : ∀ b ∈ L.own G, Whole2 w b)
    (h2 : ∀ b ∈ L.hearC G, Whole2 w b)
    (h3 : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl2 w f → Whole2 w (mk f))
    (h4 : ∀ l e, L.each G l = some e → ∀ o cl, Test2 w (e o cl))
    (h5 : ∀ l t, L.tests G l = some t → Test2 w t) : LotAll2 w L G := by
  refine ⟨fun b hb => ?_, h3, h4, h5⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact retype_whole2 (h1 b₀ h₀)
  · exact h2 b hb

/-! ### The frames -/

/-- The lot of the links' frames. -/
theorem framesLot_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotAll2 w (ProofFile.framesLot Z) G := by
  refine lotAll_of2 (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  have hb' : b ∈ P1L20.blocksOf Z := hb
  unfold P1L20.blocksOf at hb'
  split at hb'
  · rename_i fs hfs
    obtain ⟨f, hf, hb'⟩ := List.mem_flatMap.1 hb'
    obtain ⟨k1, k2, k3⟩ := H.frames hfs f hf
    unfold ProofFile.frameBlocks at hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact quiet_whole2 k1 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole2 k2 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole2 k3 (fun _ _ _ => rfl) rfl rfl
  · obtain rfl := List.mem_singleton.1 hb'
    exact quiet_whole2 refuses2 (fun _ _ _ => rfl) rfl rfl

/-! ### K1 -/

/-- A block, or one that refuses aloud where there is none. -/
theorem orLoud_at2 {n : String} {a : Place} {x : String} {o : Option (Block S Unit)}
    (h : ∀ b, o = some b → Whole2 w b) : Whole2 w (ProofFile.orLoud n a x o) := by
  cases o with
  | some b => exact h b rfl
  | none => exact quiet_whole2 refuses2 (fun _ _ _ => rfl) rfl rfl

/-- Kind K1's blocks, with the quiet step behind the reads handed in. -/
theorem k1Blocks_whole2 (H : SeatKeeps2 w) (gp : _root_.Desc.Plain.GPar) (quiet : VerifiableInference.Desc.K1.Quiet)
    (hq : ∀ G l X z, quiet G l X = some z → Whole2 w z) (G : ProofFile.Ground) :
    ∀ b ∈ VerifiableInference.Desc.K1.blocks gp quiet G, Whole2 w b := by
  intro b hb
  unfold VerifiableInference.Desc.K1.blocks at hb
  dsimp only at hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain rfl := List.mem_singleton.1 hb
    exact H.k1First _ _
  · obtain ⟨⟨X, l⟩, -, hb⟩ := List.mem_flatMap.1 hb
    dsimp only at hb
    split at hb
    · cases hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · split
        · rename_i z hz
          exact andThen_whole2 _ _ _ (H.k1Later _ _ _ _ _ _) (hq _ _ _ z hz)
        · exact H.k1Later _ _ _ _ _ _
      · exact H.k1Later _ _ _ _ _ _

/-- Kind K1's lot. -/
theorem k1Pure_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (ProofFile.k1Pure Z) G := by
  refine lotAll_of2 (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  unfold ProofFile.k1Pure VerifiableInference.Desc.K1.lotWith at hb
  dsimp only at hb
  refine k1Blocks_whole2 H _ _ (fun G l X z hz => ?_) G b hb
  cases hz
  exact orLoud_at2 fun b hb => H.reads hb

/-! ### K2 -/

/-- The finish's place: it stands behind the last link. -/
theorem finishPlace_whole2 (H : SeatKeeps2 w) (Hr : SeatRest2 w) (p : VerifiableInference.Desc.First.K2.P2) :
    Whole2 w (VerifiableInference.Desc.First.K2.finishPlace p : Block S Unit) :=
  whole_same2 (andThen_whole2 p.name _ _
    (andThen_whole2 p.name
      (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece
        VerifiableInference.Desc.First.K2.finishFrontQ) _
      (quiet_whole2 Hr.finFront (fun _ _ _ => rfl) rfl rfl) (H.k2 p))
    (quiet_whole2 (b := roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece
      VerifiableInference.Desc.First.K2.finishBehindQ) Hr.finBehind (fun _ _ _ => rfl) rfl rfl)) rfl
    (fun _ hx => hx) rfl

/-- Kind K2's lot. -/
theorem k2Pure_keeps2 (H : SeatKeeps2 w) (Hr : SeatRest2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotAll2 w (ProofFile.k2Pure Z) G := by
  refine lotAll_of2 (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hb'
  split
  · exact quiet_whole2 refuses2 (fun _ _ _ => rfl) rfl rfl
  · rename_i x hfind
    cases hx : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact quiet_whole2 refuses2 (fun _ _ _ => rfl) rfl rfl
    | some b₀ =>
      show Whole2 w b₀
      unfold P1K2.pureAt at hx
      dsimp only at hx
      split at hx
      · cases hx
        exact whole_same2 (finishPlace_whole2 H Hr x.2) rfl (fun _ hx => hx) rfl
      · obtain ⟨P, -, rfl⟩ := Option.map_eq_some_iff.1 hx
        exact whole_same2 (andThen_whole2 x.1.name (VerifiableInference.Desc.First.K2.codeSwitchKind x.2)
          (VerifiableInference.Desc.First.K2.headOpened x.1.name x.1.place P) (H.k2 _)
          (quiet_whole2 (H.openQ P) (fun _ _ _ => rfl) rfl rfl)) rfl (fun _ hx => hx) rfl
      · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 ho
        cases e
        exact whole_same2 (H.k2 x.2) rfl (fun _ hx => hx) rfl

/-! ### The lots of blocks with runs -/

/-- Kind K3's lot: at its own readers. -/
theorem k3Lot_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (K3Lot.lot Z) G := by
  refine lotAll_of2 (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  exact H.k3 Z b hb

/-- Kind K4's lot. -/
theorem k4Lot_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (ProofFile.k4Lot Z) G := by
  refine lotAll_of2 (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
  exact whole_same2 (H.k4 _) rfl (fun _ hx => hx) rfl

/-- Kind K5's lot. -/
theorem k5LotN_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (H2K5.lotN Z) G := by
  refine lotAll_of2 (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ H2K5.k5OwnN Z G from hb)
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 e
  exact whole_same2 (H.k5 _ _ _ _ e₀) rfl (fun _ hx => hx) rfl

/-- Kind K8's lot. -/
theorem k8Lot_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (ProofFile.P1K8.lot Z) G := by
  refine lotAll_of2 (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show b ∈ ProofFile.k8Whole Z G from hb)
  exact H.k8 _

/-- Kind K11's lot. -/
theorem k11Lot_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (K11.lot Z) G := by
  refine lotAll_of2 (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact H.k11 _

/-- Kind K6's lot. -/
theorem k6Lot_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (P4.k6Lot Z) G := by
  refine lotAll_of2 (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  have hb' : b ∈ P4.k6Hear Z G := hb
  unfold P4.k6Hear at hb'
  obtain ⟨ms, -, e⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 hb')
  exact H.k6 e

/-! ### K9 with K10's closing -/

/-- Kind K9's lot: the closing's three blocks, the batching, and the link's two tests. -/
theorem k9Ninth_keeps2 (H : SeatKeeps2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotAll2 w (ProofFile.k9Ninth Z) G := by
  refine lotAll_of2 (fun b hb => ?_) (fun _ hb => nomatch hb) (fun a mk h f hf => ?_) (fun l e h => ?_)
    (fun l t h => H.tests Z l t h)
  · unfold ProofFile.k9Ninth at hb
    dsimp only at hb
    obtain ⟨x, -, hb⟩ := List.mem_flatMap.1 hb
    split at hb
    · exact H.closeOf _ _ b hb
    · obtain rfl := List.mem_singleton.1 hb
      exact quiet_whole2 refuses2 (fun _ _ _ => rfl) rfl rfl
  · unfold ProofFile.k9Ninth at h
    dsimp only at h
    split at h
    · obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · cases h
        exact H.batch p hf
      · cases h
    · cases h
  · unfold ProofFile.k9Ninth at h
    dsimp only at h
    obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact H.each _

/-! ### The place "H:1" -/

/-- The block at "H:1": the step that enters the head's link, guarded, then kind K7's block. -/
theorem h1_whole2 (H : SeatKeeps2 w) (G : ProofFile.Ground) : ∀ b ∈ ProofFile.h1Own G, Whole2 w b := by
  intro b hb
  unfold ProofFile.h1Own at hb
  obtain rfl := List.mem_singleton.1 hb
  exact andThen_whole2 _ _ _
    (guarded_whole2 _ _ (sameReply2 H) (quiet_whole2 (H.front _) (fun _ _ _ => rfl) rfl rfl)) (H.k7 _ _)

/-! ### Behind the last link -/

/-- Kind K12's lot: its one block stands behind the last link and is of a kind, so nothing is asked of it. -/
theorem k12Lot_keeps2 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotKeeps2 w (VerifiableInference.Desc.K12.lot Z) G := by
  refine lot_of2 (fun b hb ha => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  unfold Meaning.K2.Asked at ha
  rw [Meaning.K2.atFinish_place] at ha
  rcases ha with h | h
  · exact absurd rfl h
  · exact absurd h (by decide)

/-- The lot of kind K13's batching: nothing is asked of it, as of kind K12's. -/
theorem k13Lot_keeps2 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotKeeps2 w (VerifiableInference.Desc.K13.lot Z) G := by
  refine lot_of2 (fun b hb ha => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  rcases ha with h | h
  · exact absurd rfl h
  · cases h

/-- The lot of W's sending: nothing is asked of it, as of kind K12's. -/
theorem k13Lot4_keeps2 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotKeeps2 w (VerifiableInference.Desc.K13.lot4 Z) G := by
  refine lot_of2 (fun b hb ha => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  have hx' : VerifiableInference.Desc.K13.wBlock Z = some x := Option.mem_toList.1 hx
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hx'
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hx'
  rcases ha with h | h
  · exact absurd rfl h
  · cases h

/-- The seal hands the state back, or refuses by what it asks. -/
theorem seal_fn2 (Hr : SeatRest2 w) : Fn2 w fun s => (ChainEnd.refuse (endAsks s)).map fun _ => s := by
  intro s s' hw
  have e : endAsks s = endAsks s' := (Hr.sealAsks s).symm.trans ((congrArg endAsks hw).trans (Hr.sealAsks s'))
  show AlikeE w ((ChainEnd.refuse (endAsks s)).map fun _ => s) ((ChainEnd.refuse (endAsks s')).map fun _ => s')
  rw [e]
  cases ChainEnd.refuse (endAsks s') with
  | error m => exact AlikeE.error m
  | ok u => exact AlikeE.ok hw

/-- The lot of the first chain's end. -/
theorem k13LotEnd_keeps2 (Hr : SeatRest2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotAll2 w (VerifiableInference.Desc.K13.lotEnd Z) G := by
  refine lotAll_of2 (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact quiet_whole2 (seal_fn2 Hr) (fun _ _ _ => rfl) rfl rfl

/-! ## 5 The seat -/

/-- **The proof file's seat: what is asked of its lots holds.** -/
theorem thePure_keeps2 (H : SeatKeeps2 w) (Hr : SeatRest2 w) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotsKeep2 w (ProofFile.onlineFirstChainBlockTables Z) G := by
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotKeeps2 w L G := by
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact (framesLot_keeps2 H Z G).keep
    · exact (k1Pure_keeps2 H Z G).keep
    · exact (k2Pure_keeps2 H Hr Z G).keep
    · exact (k3Lot_keeps2 H Z G).keep
    · exact (k4Lot_keeps2 H Z G).keep
    · exact (k5LotN_keeps2 H Z G).keep
    · exact (k8Lot_keeps2 H Z G).keep
    · exact (k9Ninth_keeps2 H Z G).keep
    · exact (k11Lot_keeps2 H Z G).keep
    · exact k12Lot_keeps2 Z G
    · exact k13Lot_keeps2 Z G
    · exact k13Lot4_keeps2 Z G
    · exact (k13LotEnd_keeps2 Hr Z G).keep
    · exact (k6Lot_keeps2 H Z G).keep
    · exact LotAll2.keep (lotAll_of2 (fun b hb => h1_whole2 H G b hb) (fun _ hb => nomatch hb)
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h))
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2.1, fun L hL => (key L hL).2.2.1,
    fun L hL => (key L hL).2.2.2⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.face2
#print axioms ProofFile.Honest.K10.test_ok2
#print axioms ProofFile.Honest.K10.fill_keeps2
#print axioms ProofFile.Honest.K10.chainBy_front2
#print axioms ProofFile.Honest.K10.LotsKeep2
#print axioms ProofFile.Honest.K10.Each2
#print axioms ProofFile.Honest.K10.partsAt_roadW2
#print axioms ProofFile.Honest.K10.partsAt_each2
#print axioms ProofFile.Honest.K10.partsAt_tests2
#print axioms ProofFile.Honest.K10.partsAt_frames2
#print axioms ProofFile.Honest.K10.partsAt_base2
#print axioms ProofFile.Honest.K10.SeatKeeps2
#print axioms ProofFile.Honest.K10.SeatRest2
#print axioms ProofFile.Honest.K10.failed_of
#print axioms ProofFile.Honest.K10.reply_of
#print axioms ProofFile.Honest.K10.sameReply2
#print axioms ProofFile.Honest.K10.LotKeeps2
#print axioms ProofFile.Honest.K10.lot_of2
#print axioms ProofFile.Honest.K10.LotAll2
#print axioms ProofFile.Honest.K10.LotAll2.keep
#print axioms ProofFile.Honest.K10.lotAll_of2
#print axioms ProofFile.Honest.K10.framesLot_keeps2
#print axioms ProofFile.Honest.K10.orLoud_at2
#print axioms ProofFile.Honest.K10.k1Blocks_whole2
#print axioms ProofFile.Honest.K10.k1Pure_keeps2
#print axioms ProofFile.Honest.K10.finishPlace_whole2
#print axioms ProofFile.Honest.K10.k2Pure_keeps2
#print axioms ProofFile.Honest.K10.k3Lot_keeps2
#print axioms ProofFile.Honest.K10.k4Lot_keeps2
#print axioms ProofFile.Honest.K10.k5LotN_keeps2
#print axioms ProofFile.Honest.K10.k8Lot_keeps2
#print axioms ProofFile.Honest.K10.k11Lot_keeps2
#print axioms ProofFile.Honest.K10.k6Lot_keeps2
#print axioms ProofFile.Honest.K10.k9Ninth_keeps2
#print axioms ProofFile.Honest.K10.h1_whole2
#print axioms ProofFile.Honest.K10.k12Lot_keeps2
#print axioms ProofFile.Honest.K10.k13Lot_keeps2
#print axioms ProofFile.Honest.K10.k13Lot4_keeps2
#print axioms ProofFile.Honest.K10.seal_fn2
#print axioms ProofFile.Honest.K10.k13LotEnd_keeps2
#print axioms ProofFile.Honest.K10.thePure_keeps2
