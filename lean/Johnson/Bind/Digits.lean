-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Digits.lean: THE LIBRARY'S WORD OF A CELL, AT A MATRIX OF INTEGERS, BY A TEXT WITHOUT
THE FIELD. The proof of `EntryAgrees` (Johnson/Bind/ColumnDefs.lean), general in the sizes.

Why. The library lays a matrix of cells over the extension field into a table's rows
(`cellEntry`, Johnson/Flat/CodingCells.lean). A committer that runs reads words. At a matrix whose
cells are casts of integers (the digits of weights are such) the word is the integer's least residue
modulo the prime, and the address is plain arithmetic.

Main names (namespace `Bind.Column`).
  `ofF_intCast`: the word of an integer's class is the integer's least residue.
  `ofF_zero`: the word of 0 is 0.
  **`entryAgrees`**: `EntryAgrees S Z cut N`, if the matrix's cells fit a row's message before the
    pads (hfit). At the two sizes that premise is paid (`full_fits`, `small_fits`,
    Johnson/Flat/ClaimsSizes.lean).

Limits. Those of Johnson/Bind/ColumnDefs.lean. That a program lays its digits at these addresses is
not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.ColumnDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Column
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape

/-- The word of an integer's class modulo the prime is the integer's least residue. -/
theorem ofF_intCast (d : ℤ) :
    OnBytes.Slice.ofF ((d : ℤ) : GF) = UInt64.ofNat (d % (Code.pGold : ℤ)).toNat := by
  have h : ((((d : ℤ) : GF).val : ℕ) : ℤ) = d % (Code.pGold : ℤ) := ZMod.val_intCast d
  unfold OnBytes.Slice.ofF
  rw [← h, Int.toNat_natCast]

/-- The word of 0 is 0. -/
theorem ofF_zero : OnBytes.Slice.ofF (0 : GF) = 0 := by
  unfold OnBytes.Slice.ofF
  rw [ZMod.val_zero]
  rfl

/-- **The digits.** -/
theorem entryAgrees (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (hfit : N.rows * 2 ^ N.kLo ≤ cut) : EntryAgrees S Z cut N := by
  intro M mat hM b e
  unfold cellEntry cellEntryAt
  by_cases hc : e < cut
  · rw [if_pos hc]
    by_cases hd : e / 2 ^ N.kLo < N.rows ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo < 2 ^ (N.kLo + S.P.v)
    · rw [dif_pos hd, if_pos hd, ← ofF_intCast]
      refine congrArg OnBytes.Slice.ofF ?_
      have hcell : M ⟨_, hd.1⟩ ⟨_, hd.2⟩ = algebraMap GF GE
          ((mat (e / 2 ^ N.kLo) (b * 2 ^ N.kLo + e % 2 ^ N.kLo) : ℤ) : GF) := by
        rw [hM, map_intCast]
      show (M ⟨_, hd.1⟩ ⟨_, hd.2⟩).c0 = _
      rw [hcell]
      rfl
    · rw [dif_neg hd, if_neg hd]
  · have hr : ¬ e / 2 ^ N.kLo < N.rows := fun hlt =>
      hc (lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).1 hlt) hfit)
    rw [if_neg hc, if_neg fun hd => hr hd.1]
    split
    · exact ofF_zero
    · rfl

end Bind.Column

end

#print axioms Bind.Column.ofF_intCast
#print axioms Bind.Column.ofF_zero
#print axioms Bind.Column.entryAgrees
