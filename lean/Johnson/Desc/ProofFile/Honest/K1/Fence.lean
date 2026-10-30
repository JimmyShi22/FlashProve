-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Fence.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR THE
HONEST SIDE: THE FREE ENTRIES OF A SAMPLED MESSAGE's MASK ROWS: BELOW THEIR COUNT AN ENTRY IS A COIN
AND IS NO PAD's PLACE. Statements and proofs.

The count is the verifier's ledger's own: OnBytes.Send.freeMaskEntries m ell s
(OnBytes/Iop/Send.lean): 0 where m = 0 or ell < s; else m * (ell - s) + (m - 1): the entries whose
number lies below that of the pad's first entry, which is entry ell - s of row m - 1. Kin, with the
same term: Fmt.Places.freeCount (Fmt/Places.lean), freeEntries (Johnson/Desc/Ok/Links.lean). An
entry's number: entry c of row rho of m rows: c * m + rho.

  free_lt       at 1 ≤ s a number below the count is the number of an entry: it lies below m * ell
  free_not_pad  a number below the count is not the number (ell - s + i) * m + (m - 1) of a pad's
                place, whatever i
  held_free     under sendFits (Honest/K1/Coins.lean), at a sampled message, at a number j below the
                count: the held word, in the mask table, at the index of the entry with the number j
                is the part's coin number maskStart + j, AND THAT INDEX IS NO ENTRY OF K1.Msg.pad i
                (Johnson/Desc/K1/Own.lean), whatever i

Limits. What is WRITTEN where: no sentence on what a coin is for. At a message without a sample
(s = 0) the count's term overshoots the table by m - 1: no law here speaks of such a message. That a
later step takes the free entries by increasing number, each once, is not said here. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PadLaw
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt split_index)

/-- At 1 ≤ s a number below the count is the number of an entry. -/
theorem free_lt (m ell s j : Nat) (hs : 1 ≤ s) (h : j < OnBytes.Send.freeMaskEntries m ell s) :
    j < m * ell := by
  unfold OnBytes.Send.freeMaskEntries at h
  split_ifs at h with hc
  · exact absurd h (Nat.not_lt_zero _)
  · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at hc
    have e : m * ell = m * (ell - s) + m * s := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hc.2]
    have : m ≤ m * s := Nat.le_mul_of_pos_right _ hs
    omega

/-- A number below the count is no pad's place's number. -/
theorem free_not_pad (m ell s i j : Nat) (h : j < OnBytes.Send.freeMaskEntries m ell s) :
    j ≠ (ell - s + i) * m + (m - 1) := by
  unfold OnBytes.Send.freeMaskEntries at h
  split_ifs at h
  · exact absurd h (Nat.not_lt_zero _)
  · have h2 : m * (ell - s) ≤ (ell - s + i) * m := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega

/-- **The fence.** -/
theorem held_free (w : Words GE) (first : Nat) (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k j : Nat)
    (hf : sendFits P ride = true) (hk : k < P.sent.size) (ha : (shapeAt P k).answers ≠ 0)
    (hj : j < OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell (shapeAt P k).answers) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .mask
        (j % (shapeAt P k).maskRows +
          j / (shapeAt P k).maskRows * 2 ^ K1.clog (shapeAt P k).maskRows) =
      ce cs (maskStart P ride k + j) ∧
    ∀ i x, x ∈ (K1.Msg.of P.codes (shapeAt P k)).pad i →
      x.1 ≠ j % (shapeAt P k).maskRows +
        j / (shapeAt P k).maskRows * 2 ^ K1.clog (shapeAt P k).maskRows := by
  have hr := fits_noRide P ride k hf hk ha
  have hj' : j < (shapeAt P k).maskRows *
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell :=
    free_lt _ _ _ j (Nat.pos_of_ne_zero ha) hj
  have hm : 0 < (shapeAt P k).maskRows := by
    rcases Nat.eq_zero_or_pos (shapeAt P k).maskRows with h0 | h0
    · rw [h0, Nat.zero_mul] at hj'
      exact absurd hj' (Nat.not_lt_zero _)
    · exact h0
  refine ⟨(held_slot_in w first P ride data cs k j hk hr hj').trans (ce_eq _ cs _ _).symm,
    fun i x hx he => ?_⟩
  rw [pad_mask_at P.codes _ i (fits_lengths P ride hf)
    (fits_maskCode P ride k hf hk (Nat.ne_of_gt hm)) (Nat.ne_of_gt hm)] at hx
  obtain rfl := List.mem_singleton.1 hx
  have a := split_index ((shapeAt P k).maskRows - 1)
    ((P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i)
    (shapeAt P k).maskRows (by omega)
  have b := split_index (j % (shapeAt P k).maskRows) (j / (shapeAt P k).maskRows)
    (shapeAt P k).maskRows (Nat.mod_lt _ hm)
  rw [show (shapeAt P k).maskRows - 1 +
      ((P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i) *
        2 ^ K1.clog (shapeAt P k).maskRows = _ from he] at a
  have h1 : j % (shapeAt P k).maskRows = (shapeAt P k).maskRows - 1 := b.1.symm.trans a.1
  have h2 : j / (shapeAt P k).maskRows =
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i :=
    b.2.symm.trans a.2
  have h3 := Nat.div_add_mod j (shapeAt P k).maskRows
  rw [h1, h2, Nat.mul_comm] at h3
  exact free_not_pad _ _ _ i j hj h3.symm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.free_lt
#print axioms ProofFile.Honest.K1.free_not_pad
#print axioms ProofFile.Honest.K1.held_free
