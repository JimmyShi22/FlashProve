-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Fill/TiesP1.lean: what one of the layer's sentences, and a fact on the index masks'
ledger, give the merge of the claims on the committed table. Theorems with their proofs.

Main names:
  `entry_of_room`: where `roomIsB` (Johnson/Top/H0/Walk/FrameEntriesDefs.lean) says yes at the
    verifier's state and the planner's number of entries left at the segment is not 0, the index
    masks' ledger has an entry to give (`EntryAt`, Johnson/Top/H0/MergeLaw/OffRecord.lean).
  `woHere_of_fillR`: "wo", with `hasRow`, gives the merge's own sentence `WoHere` at the numbers
    that are read off the verifier's state: where the layer's layout is the merge's and the index
    masks' ledger gives the entry c next, under two facts on the pile's reader.

Limits. `roomIsB` is no item of the table any more: who shows it at the states that are reached is
not said here. Nothing on soundness.

-/
import Johnson.Top.H0.Fill.FillP1
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.FillP1
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading WsShape wsLayOf)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K13.Law (lowBits)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.Walk.Law (hasRow)

/-- **What the fact on the index masks' ledger gives whoever opens "wo"**: where the plan's number
of entries left at the segment is not 0, the index masks' ledger in the verifier's state has an
entry to give. -/
theorem entry_of_room {free0 : ℕ} {fvs : List Bool} {m : ℕ} {s : S}
    (h : Johnson.Desc.First.Walk.Tied.roomIsB free0 fvs m s = true)
    (hp : 0 < free0 - Johnson.Desc.First.Walk.Tied.rowsBefore fvs m) : ∃ c, EntryAt s c := by
  unfold Johnson.Desc.First.Walk.Tied.roomIsB Johnson.Desc.First.Walk.Tied.leftIsB at h
  cases hl : Johnson.Desc.First.Walk.Law.ledgerAt s with
  | none => simp [hl] at h
  | some l =>
    rw [hl] at h
    simp only [Option.any_some, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    have ht : (VerifiableInference.Desc.First.Pend.takeEntry l).isSome = true := by
      unfold VerifiableInference.Desc.First.Pend.takeEntry
      have h0 : 0 < l.left := by rw [h.2]; exact hp
      simp [h.1, h0]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ht
    exact ⟨x.1, l, x.2, hl, hx⟩

/-- **THE MERGE's THIRD TIE's HALF ON "wo"**: the table's sentence, with the public item that is
tied to it, gives `WoHere` at the numbers that are read off the verifier's state: under two facts on
letters: the pile's matrix is the cells; its mask entries of the index masks' message are idx. -/
theorem woHere_of_fillR {P W : Type} (Pm : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ}
    (h : wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni : ℕ)
    (ui : Fin Pm.lay.U.size) (sv : ℕ) (hsv : sv < Pm.nMsg) (c : ℕ) (hc : c < ni)
    (d : PubData) (hlay : d.lay = Pm.lay) (rw : P × S → W → PileWit d.lay.m0 d.lay.lk) (m : ℕ)
    (a : P × S) (y : Strs) (w : W) (cell : ℕ → ℕ → GE) (idx : ℕ → GE) (hw : woAt d rw m a y w)
    (hr : hasRow d.lay (d.ncl m) d.lin a.2 = true) (he : EntryAt a.2 c)
    (hmat : ∀ (i : Fin d.lay.m0) (C : ℕ), C < 2 ^ d.lay.lk →
      (rw a w).mat i (lowBits d.lay.lk C) = cell i C)
    (hmask : ∀ c', (rw a w).mask ⟨a.2.out.indexMasks, c'⟩ = idx c') :
    WoHere (recNums Pm h hn ni ui sv hsv c hc) (d.ncl m) d.lin cell idx a.2 := by
  obtain ⟨lay, lin, ncl⟩ := d
  simp only at hlay
  subst hlay
  unfold hasRow at hr
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 hr
  exact ⟨r, rw a w, hr', fun l c' l' e1 e2 => he.unique ⟨l, l', e1, e2⟩, hmat, hmask, hw r hr'⟩

end VerifiableInference.Desc.First.FillP1

#print axioms VerifiableInference.Desc.First.FillP1.entry_of_room
#print axioms VerifiableInference.Desc.First.FillP1.woHere_of_fillR
