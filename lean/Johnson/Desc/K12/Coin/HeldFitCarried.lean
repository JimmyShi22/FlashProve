-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/HeldFitCarried.lean: **WHAT THE RIDING OF "THE RECORD HOLDS THE SAMPLE" ASKS OF THE RECORD IN FRONT (HeldFit, HeldThrough.lean) IS A TEST WITH CODE THAT EVERY BLOCK OF THE SHARED CHAIN HANDS
ON: A FIFTH BOOL BESIDE "shape k".** One definition with code; statements and proofs, in the blocks' own decide-form.
  fitX d        every place of the book names a tree of the book, and the book places no message that the statement has not. THE SAME TEST AT EVERY BORDER.
  fitX_iff      it is HeldFit.
  fitX_first · fitX_front · fitX_k14 · fitX_onGu · fitX_onGomega   every block hands it on.
Limits. At the chain's own record St. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.HeldThrough
import Johnson.Desc.Sound.SeatsCarried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Out (k12_out3)
open VerifiableInference.Desc.Sound (PlacesInBook placesIn_empty recvBook)
open _root_.Desc.K14 (St P14)
open _root_.Desc.K14.Law.Fence (own_leave send_first keepsSmp_k14 bookStep_front recvBook_counts)

/-- **THE FIFTH BOOL BESIDE "shape k".** -/
def fitX (d : St) : Bool :=
  (d.book.place.all fun q => decide (q.1 < d.book.trees.size)) &&
    decide (d.book.place.size ≤ d.st.oracles.size)

theorem fitX_iff (d : St) : fitX d = true ↔ HeldFit d := by
  unfold fitX HeldFit PlacesInBook
  rw [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem]
  refine and_congr_left fun _ => ⟨fun h o q hq => ?_, fun h q hq => ?_⟩
  · exact of_decide_eq_true (h q (Array.mem_of_getElem? hq))
  · obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hq
    exact decide_eq_true (h i q (by rw [Array.getElem?_eq_getElem hi, e]))

theorem fitX_first (codes : Codes) (key : TableKey) : fitX (_root_.Desc.K14.first codes key) = true :=
  (fitX_iff _).2 ⟨placesIn_empty, Nat.le_refl _⟩

theorem fitX_front (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (_root_.Desc.K14.frontBlock c).decide d rs gs = .ok d') (hX : fitX d = true) :
    fitX d' = true := by
  rw [bookStep_front c d d' rs gs h]
  exact hX

/-- **K14's eight blocks hand it on.** -/
theorem fitX_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : _root_.Desc.K14.blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d') (hX : fitX d = true) :
    fitX d' = true := by
  obtain ⟨f1, f2⟩ := (fitX_iff d).1 hX
  have ks := keepsSmp_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb d d' rs gs h
  refine (fitX_iff d').2 ?_
  have own : (b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8) → HeldFit d' := fun hq => by
    have e := (own_leave P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h).1
    unfold HeldFit
    rw [e]
    exact ⟨f1, f2.trans ks.2.1⟩
  have snd : (b = b2 ∨ b = b5) → HeldFit d' := fun hq => by
    obtain ⟨sent, lay, hl, _, r3, rb, _⟩ := send_first P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
    unfold HeldFit
    rw [rb, r3, (recvBook_counts _ d.book sent lay _ _).1]
    exact ⟨(placesGrow_recv _ d.book sent lay _ _
      fun i hi => OnBytes.Tie.Pv.Keeps.Fit.lay_lt hl hi).inB f1, by omega⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with e | e | e | e | e | e | e | e
  · exact own (.inl e)
  · exact snd (.inl e)
  · exact own (.inr (.inl e))
  · exact own (.inr (.inr (.inl e)))
  · exact snd (.inr e)
  · exact own (.inr (.inr (.inr (.inl e))))
  · exact own (.inr (.inr (.inr (.inr (.inl e)))))
  · exact own (.inr (.inr (.inr (.inr (.inr e)))))

/-- At the shared chain's two seats. -/
theorem fitX_seat (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Block T12 Unit) Seat.leave).decide d rs
      gs = .ok d') (hX : fitX d = true) : fitX d' = true := by
  have hg := seat_places g mask p he ha d d' rs gs h
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  have o3 := k12_out3 p he ha _ t' rs gs ht'
  exact (fitX_iff _).2 ⟨hg.inB ((fitX_iff d).1 hX).1, Nat.le_of_eq o3.step.symm⟩

theorem fitX_onGu (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d')
    (hX : fitX d = true) : fitX d' = true := fitX_seat _ _ p he ha d d' rs gs h hX

theorem fitX_onGomega (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d')
    (hX : fitX d = true) : fitX d' = true := fitX_seat _ _ p he ha d d' rs gs h hX

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.fitX_iff
#print axioms VerifiableInference.Desc.K12.Coin.fitX_k14
#print axioms VerifiableInference.Desc.K12.Coin.fitX_onGu
#print axioms VerifiableInference.Desc.K12.Coin.fitX_onGomega
