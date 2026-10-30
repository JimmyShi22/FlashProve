-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/MaskLaw.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: WHICH COIN STANDS AT WHICH ENTRY OF A MESSAGE's MASK ROWS: for a message whose
table does not ride. A definition, statements and proofs, on rowsR and dueR (Honest/K1/Coins.lean)
and on the core's held words (Johnson/Prover/Send/Core.lean, Held.lean).

  maskStart     where, among the part's coins of the extension field, the entries of message number
                k's mask rows begin
  ce_eq         below the count ce is the coin itself
  mask_coin     entry c of mask row rho IS the coin number maskStart + c * m + rho (m rows)
  mask_slot     the same BY THE FORMAT's OWN NUMBER j = c * m + rho of an entry of the mask rows
  startR_succ, startR_mono, mask_in   these numbers lie inside the part's count
  held_slot, held_slot_in   the held word of message number first + k, in its mask table, at the
                index of the entry with the format's number j, IS the part's coin number
                maskStart + j

Limits. What is WRITTEN where: no sentence on what a mask row or a coin is for. THE LAWS HOLD FOR
ALL ENTRIES OF THE MASK ROWS, A PAD's OWN PLACES AMONG THEM: "below the free entries' count" is the
book's maker's premise, to be named where a spender's entry is taken: it is not in these laws: AS A
STATEMENT IT STANDS IN Honest/K1/Fence.lean (held_free). j IS THE FORMAT's NUMBER c * m + rho OF AN
ENTRY: that a ledger's slot number in the verifier's statement is that number is NOT said here. The
book's entries (owner, start, count) are the book's maker's: that an entry's start is maskStart + a
slot's number is not said here. A riding table is laid otherwise (Ride.lay; ride_coin,
Honest/K1/RideLaw.lean). Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Prover.Send.Held

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- Where, among the part's coins of E, the entries of message number k's mask rows begin. -/
def maskStart (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) : Nat :=
  (startR P ride k).e + if (shapeAt P k).mainDeg == 3 then
    (stepsOf P.codes (shapeAt P k) (ride k)).main else 0

/-- Below the count ce is the coin itself. -/
theorem ce_eq (d : Due) (cs : Cs d) (i : Nat) (h : i < d.e) : ce cs i = cs.e ⟨i, h⟩ := dif_pos h

/-- **Entry c of mask row rho is the coin number maskStart + c * m + rho.** -/
theorem mask_coin (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k ρ c : Nat)
    (hr : ride k = none) (hρ : ρ < (shapeAt P k).maskRows)
    (hc : c < (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    (rowsR P ride data cs k).mask ρ c =
      ce cs (maskStart P ride k + c * (shapeAt P k).maskRows + ρ) := by
  simp only [rowsR, hr]
  rw [if_pos ⟨hρ, hc⟩]
  simp only [maskStart, hr]

/-- **By the format's own number of an entry of the mask rows.** -/
theorem mask_slot (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k j : Nat)
    (hr : ride k = none)
    (hj : j < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    (rowsR P ride data cs k).mask (j % (shapeAt P k).maskRows) (j / (shapeAt P k).maskRows) =
      ce cs (maskStart P ride k + j) := by
  have hm : 0 < (shapeAt P k).maskRows := by
    rcases Nat.eq_zero_or_pos (shapeAt P k).maskRows with h0 | h0
    · rw [h0, Nat.zero_mul] at hj
      exact absurd hj (Nat.not_lt_zero _)
    · exact h0
  rw [mask_coin P ride data cs k _ _ hr (Nat.mod_lt _ hm) (Nat.div_lt_of_lt_mul hj),
    Nat.add_assoc, Nat.div_add_mod']

/-- The next message's coins begin behind this message's. -/
theorem startR_succ (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) :
    startR P ride (k + 1) = (startR P ride k).plus (dueMsg P.codes (shapeAt P k) (ride k)) := by
  unfold startR
  rw [List.range_succ, List.foldl_append]
  rfl

theorem startR_mono (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) :
    ∀ n, k ≤ n → (startR P ride k).e ≤ (startR P ride n).e := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih =>
    rw [startR_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- **These numbers lie inside the part's count.** -/
theorem mask_in (P : K1.Par) (ride : Nat → Option Ride) (k j : Nat) (hk : k < P.sent.size)
    (hr : ride k = none)
    (hj : j < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    maskStart P ride k + j < (dueR P ride).e := by
  have h1 := startR_mono P ride (k + 1) P.sent.size hk
  rw [startR_succ] at h1
  have h2 : (stepsOf P.codes (shapeAt P k) (ride k)).mask =
      (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
    simp only [stepsOf, hr, Option.map_none, Option.getD_none]
  unfold dueR
  refine Nat.lt_of_lt_of_le ?_ h1
  show maskStart P ride k + j < (startR P ride k).e + (dueMsg P.codes (shapeAt P k) (ride k)).e
  unfold maskStart dueMsg
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · simp only [h3, if_true]
    omega
  · simp only [h3, if_false, Bool.false_eq_true]
    omega

/-- **The sender's law on a mask row.** -/
theorem held_slot (w : Words GE) (first : Nat) (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k j : Nat)
    (hk : k < P.sent.size) (hr : ride k = none)
    (hj : j < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell)
    (hi : maskStart P ride k + j < (dueR P ride).e) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .mask
        (j % (shapeAt P k).maskRows +
          j / (shapeAt P k).maskRows * 2 ^ K1.clog (shapeAt P k).maskRows) =
      cs.e ⟨maskStart P ride k + j, hi⟩ := by
  have hm : 0 < (shapeAt P k).maskRows := by
    rcases Nat.eq_zero_or_pos (shapeAt P k).maskRows with h0 | h0
    · rw [h0, Nat.zero_mul] at hj
      exact absurd hj (Nat.not_lt_zero _)
    · exact h0
  rw [Johnson.Prover.Send.held_new w first P _ k hk,
    Johnson.Prover.Send.word_mask _ _ _ _ (Nat.mod_lt _ hm), mask_slot P ride data cs k j hr hj,
    ce_eq _ cs _ hi]

/-- The same, with the number's bound paid by mask_in. -/
theorem held_slot_in (w : Words GE) (first : Nat) (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k j : Nat)
    (hk : k < P.sent.size) (hr : ride k = none)
    (hj : j < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .mask
        (j % (shapeAt P k).maskRows +
          j / (shapeAt P k).maskRows * 2 ^ K1.clog (shapeAt P k).maskRows) =
      cs.e ⟨maskStart P ride k + j, mask_in P ride k j hk hr hj⟩ :=
  held_slot w first P ride data cs k j hk hr hj _

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ce_eq
#print axioms ProofFile.Honest.K1.mask_coin
#print axioms ProofFile.Honest.K1.mask_slot
#print axioms ProofFile.Honest.K1.startR_succ
#print axioms ProofFile.Honest.K1.startR_mono
#print axioms ProofFile.Honest.K1.mask_in
#print axioms ProofFile.Honest.K1.held_slot
#print axioms ProofFile.Honest.K1.held_slot_in
#print axioms ProofFile.Honest.K1.maskStart
