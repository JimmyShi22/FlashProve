-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PileRow.lean: A PENDING ROW's WEIGHTS AND COLUMN POINT ARE `rowReadsOf`
(PileDefs.lean of this folder) AT WHAT THE MERGE LEFT. Statements with their proofs.

Why. The one text that makes a row of the pile is `pendingRowO` (Johnson/Desc/First/Pend/Row.lean).
It also takes an entry of the index masks' ledger, and lays a shown value into the row's target. An
honest prover's parts read of a row its weights and its column point alone (`rowReads`,
PileReads.lean of this folder). `rowReadsOf` cuts these two out. The library's `pendingRowO_iff`
(Pend/RowMeans.lean) is called.
Main names:
  `rowReadsOf_row`: **wherever `pendingRowO` returns a row, `rowReadsOf` at what the merge left
    returns that row's weights and column point.**
  `pendingRowO_of_reads`: the way back: where `rowReadsOf` returns and the ledger has an entry to
    take, `pendingRowO` returns a row with these two.

What is not claimed. What the weights mean. That any state of a run holds such claims. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.PileDefs
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Desc.K13.Honest.PileReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First.Pend (pendingRowO span addClaim takeEntry pendingRowO_iff)

/-- **Wherever `pendingRowO` returns a row, `rowReadsOf` returns its weights and column point.** -/
theorem rowReadsOf_row {lay : WsLay} {im : ℕ} {o : WsForkOut} {n : ℕ} {S : LinShape}
    {os os' : Array OnBytes.Oracle} {r : TensorRow}
    (h : pendingRowO lay im o n S os = .ok (r, os')) :
    rowReadsOf lay S n o.recs o.rm = some (rowReads r) := by
  obtain ⟨h4, h5, h6, h7, first, last, hs, h9, h10, h11, h12, Gamma, hG, g, hg, _, _, _, _, _, rfl,
    _⟩ := (pendingRowO_iff lay im o n S os os' r).1 h
  have h5' : o.recs.isEmpty = false := by
    cases hr : o.recs with
    | nil => exact absurd hr h5
    | cons _ _ => rfl
  unfold rowReadsOf
  rw [if_pos (by simp [h4, h5', h6, h7]), hs]
  simp only
  rw [if_pos ⟨h9, h10, h11, h12⟩, hG]
  simp only
  rw [hg]
  rfl

/-- **The way back**: where `rowReadsOf` returns and the ledger has an entry to take. -/
theorem pendingRowO_of_reads {lay : WsLay} {im : ℕ} {o : WsForkOut} {n : ℕ} {S : LinShape}
    {os : Array OnBytes.Oracle} {q : List Tensor × List E} {l l' : Ledger} {c : ℕ}
    (h : rowReadsOf lay S n o.recs o.rm = some q) (hl : (os[im]?).bind (·.ledger) = some l)
    (ht : takeEntry l = some (c, l')) :
    ∃ r os', pendingRowO lay im o n S os = .ok (r, os') ∧ rowReads r = q := by
  unfold rowReadsOf at h
  split at h
  · rename_i h0
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h0
    obtain ⟨⟨⟨h4, h5⟩, h6⟩, h7⟩ := h0
    split at h
    · rename_i first last hs
      split at h
      · rename_i h9
        split at h
        · rename_i Gamma hG
          obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 h
          refine ⟨_, _, (pendingRowO_iff lay im o n S os _ _).2 ⟨h4, ?_, h6, h7, first, last, hs,
            h9.1, h9.2.1, h9.2.2.1, h9.2.2.2, Gamma, hG, g, hg, l, hl, c, l', ht, rfl, rfl⟩, rfl⟩
          intro e
          rw [e] at h5
          cases h5
        · cases h
      · cases h
    · cases h
  · cases h

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.rowReadsOf_row
#print axioms VerifiableInference.Desc.K13.Honest.pendingRowO_of_reads
