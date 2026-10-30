-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/SeatTied.lean: K9's SEAT (`SeatedFree`, Honest/K9/AtSeatAll.lean) AND THE LIBRARY's
HEAD MEET AT ONE LINK AND ONE SET OF NUMBERS. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file,
and no goal is stated. THE BARE TIE IS THE LIBRARY's: "the chain's link l is the link that the head's data name at l",
both ways (`P5J.k03_lk_at`, Johnson/P5J/K03RidesDigAt2.lean; `LPFK9.link_of_lk`, Johnson/LPFK9R/SortTiesAtMg.lean).
WHAT IS NEW HERE: that `SeatedFree`, at which K9's payers give K9's clause, and the four seating premises of the
library's laws on a sort's runs hold at ONE Lk, p.
  **`tied_of_seated`**   under the head `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`, l < 25, from `SeatedFree cF Zp l
      k Lk p w`, AT THE CALLER's OWN LETTERS: h.𝔇.lk l = some Lk · `SegAt l (IM.subAt l) Lk` · the batching is a draw
      with the gatherer behind it (`DrawMoves` …) · `IM.k9At Zp l = some p`: the four seating premises of
      Honest/K9/KeepsAtHead.lean and KeepsDecide.lean. By the library's `LPFK9.sits_at_constant`
      (Johnson/LPFK9R/SitsAtConstant.lean): the two links are one because both are cF.links[l]?, the two sets of
      numbers because both are `IM.k9At Zp l`
  `batching_at_table`   the seated batching stands at the number under which the head's own table names it:
      cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps l]?
  **`step_leaves_lay`**, **`step_leaves_att`**, **`step_leaves_head`**   so, from the head and `SeatedFree`: every
      accepting step of the seated batching from s to s' leaves: `setLeaves s s'` (in it s'.out = s.out) at all three
      sorts; s'.own? = s.own? at a feed-forward segment; at the head's: ∀ a, s.here = .head a → ∃ a', s'.here = .head
      a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo
  **`blk_leaves_lay`**, **`blk_leaves_att`**, **`blk_leaves_head`**   THE SAME WITH NO LETTER OF K9's LEFT: under the
      head and the segment's sort: ∀ blk, cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps l]? = some blk → every accepting
      step of blk …
The letter u : HTailF2 is read by nothing in the conclusions: a caller lays any value.
On a member: the head is met under four premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z)
alone (the library's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean). `tied_of_seated` and `sub_odd` are
called also by Honest/K9/DecideTied.lean, GoodAttSeat.lean and GoodAttLook.lean, the first by GoodHead.lean and
XkBat.lean, the second by GoodAttPlan.lean too; the last three by no line.
WHAT IS NOT CLAIMED. That the seated batching's step accepts at any state. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtHead
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.LPFK9R.SitsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {l k : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
  {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **One link, one set of numbers: at the caller's own letters.** -/
theorem tied_of_seated (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) :
    h.𝔇.lk l = some Lk ∧ SegAt l (IM.subAt l) Lk ∧
      DrawMoves Desc.K9.atS p [.add (claimsInBy Lk.each Lk.hear Lk.order)] Lk.batchB ∧
      IM.k9At Zp l = some p := by
  obtain ⟨L, p', Q, hlk, hp', _, hs⟩ := LPFK9.sits_at_constant h.toAtMg l hl
  obtain rfl : L = Lk := Option.some.inj (hs.link.symm.trans Sd.link)
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans Sd.numbers)
  exact ⟨hlk, LPFK9.segAt_of_sits hs, hs.draw, hp'⟩

/-- The seated batching stands at the head's own table's number. -/
theorem batching_at_table (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) :
    cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps l]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
  rw [LPFK9.batchAt_full l hl, ← (tied_of_seated h hl Sd).2.1.hear, Sd.hears]
  exact Sd.batching

/-- **At a feed-forward segment.** -/
theorem step_leaves_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hl : l < 25)
    (hs : IM.subAt l = .layers) (Sd : SeatedFree cF Zp l k Lk p w) (u : HTailF2) (ft : ℕ) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', n)) :
    setLeaves s s' ∧ s'.own? = s.own? := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact bat_leaves_lay h O l hl hs Lk p hlk seg drawB kp u (k9Keeps_of_step Sd ft s s' rs cols n hy)

/-- The sort of an odd segment. -/
theorem sub_odd : ∀ g < 12, IM.subAt (2 * g + 1) = .attention := by decide

/-- **At an attention segment.** -/
theorem step_leaves_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g + 1) k Lk p w) (u : HTailF2) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', n)) : setLeaves s s' := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h (by omega) Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact bat_leaves_att h O hg (sub_odd g hg) Lk p hlk seg drawB kp u (k9Keeps_of_step Sd ft s s' rs cols n hy)

/-- **At the head's segment.** -/
theorem step_leaves_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Sd : SeatedFree cF Zp 24 k Lk p w)
    (u : HTailF2) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (n : ℕ)
    (hy : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s rs cols = .ok (s', n)) :
    setLeaves s s' ∧
      ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h (by omega) Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact bat_leaves_head h O rfl Lk p hlk seg drawB kp u (k9Keeps_of_step Sd ft s s' rs cols n hy)

/-- **With no letter of K9's left: at a feed-forward segment.** -/
theorem blk_leaves_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hl : l < 25)
    (hs : IM.subAt l = .layers) (u : HTailF2) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps l]? = some blk) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ) (hy : blk.step ft s rs cols = .ok (s', n)) :
    setLeaves s s' ∧ s'.own? = s.own? := by
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h l hl
  obtain rfl := Option.some.inj (hb.symm.trans (batching_at_table h hl Sd))
  exact step_leaves_lay h hl hs Sd u ft s s' rs cols n hy

/-- **With no letter of K9's left: at an attention segment.** -/
theorem blk_leaves_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) (u : HTailF2)
    (blk : Block S ProofFile.Cl) (hb : cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps (2 * g + 1)]? = some blk) (ft : ℕ)
    (s s' : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (n : ℕ) (hy : blk.step ft s rs cols = .ok (s', n)) :
    setLeaves s s' := by
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h (2 * g + 1) (by omega)
  obtain rfl := Option.some.inj (hb.symm.trans (batching_at_table h (by omega) Sd))
  exact step_leaves_att h hg Sd u ft s s' rs cols n hy

/-- **With no letter of K9's left: at the head's segment.** -/
theorem blk_leaves_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (u : HTailF2) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[batchAt P5J.fullLinks P5J.At.ps 24]? = some blk) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ) (hy : blk.step ft s rs cols = .ok (s', n)) :
    setLeaves s s' ∧
      ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h 24 (by omega)
  obtain rfl := Option.some.inj (hb.symm.trans (batching_at_table h (by omega) Sd))
  exact step_leaves_head h Sd u ft s s' rs cols n hy

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.tied_of_seated
#print axioms ProofFile.Honest.K9.batching_at_table
#print axioms ProofFile.Honest.K9.step_leaves_lay
#print axioms ProofFile.Honest.K9.sub_odd
#print axioms ProofFile.Honest.K9.step_leaves_att
#print axioms ProofFile.Honest.K9.step_leaves_head
#print axioms ProofFile.Honest.K9.blk_leaves_lay
#print axioms ProofFile.Honest.K9.blk_leaves_att
#print axioms ProofFile.Honest.K9.blk_leaves_head
