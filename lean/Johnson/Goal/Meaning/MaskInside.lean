-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/MaskInside.lean: an entry of a mask row that the ledger gives out lies inside
its oracle message's ranges and off the pad of its out-of-domain (OOD) sample. Theorems, proved; an
example and three negative examples, evaluated by Lean's kernel.

Why. Johnson/Goal/Meaning/LaidInside.lean says of the MAIN rows that an element of an array of the
layout lies inside its message's ranges and off the pad. The MASK rows have no layout: the programs'
ledger of hidden scalars gives out their entries by number: 0, 1, … below `Send.freeMaskEntries
maskRows ell answers` (OnBytes/Iop/Send.lean): "all below the first place of the pad, which is at
the end of the last row. In an index the row's number is low". A reader of a witness takes entry J
of a mask table as row J % 2 ^ rowBits, place J / 2 ^ rowBits (`tabQ`,
Johnson/Desc/Sound/FormsQ.lean). A pin fixes a message inside its ranges alone (`InMsg`,
Johnson/Desc/Sound/World.lean), and at the pad's place each copy of a message has an entry of its
own (`padB`, Johnson/Desc/SeatAt.lean). So a statement on what is read at a mask entry says
something of the committed message only where the entry lies inside the ranges and off the pad.

Main names:
  mask_arith   the arithmetic, on four numbers.
  mask_geometry   s.maskRows a power of two, s.answers at least 1, J below freeMaskEntries: then the
  row is below s.maskRows, the place below the mask code's message length, and padB rejects.
  mask_inside   the same with InMsg. mask_met   all premises hold together: one mask row of eight
  places, one answer: J = 6. tooth_rows   three mask rows (no power of two): J = 3 is below
  freeMaskEntries, and its row, 3, is not below 3. tooth_answers   no answer: J = 7 is below
  freeMaskEntries, and padB accepts its place (padB says of itself "at one answer"). tooth_free   J
  = freeMaskEntries at the example: padB accepts its place.
So none of the three premises can be dropped.

What is not claimed. That every mask entry which some statement reads has a number below
freeMaskEntries: that is a matter of the reader's number of slots. That a real message's number of
mask rows is a power of two. The example's numbers are made up. Nothing on soundness, nothing on
hiding. The program does not import this file.
-/
import OnBytes.Iop.Send
import Johnson.Desc.SeatAt
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning

open OnBytes
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.Sound (InMsg)

/-- The arithmetic. R: the rows; L: a row's places; a: the places of the pad, at the end of the last
row; J: an index in which the row's number is low. -/
theorem mask_arith (R L a J : ℕ) (hR : 0 < R) (ha : 1 ≤ a) (haL : a ≤ L)
    (hJ : J < R * (L - a) + (R - 1)) :
    J % R < R ∧ J / R < L ∧ ¬ (J % R + 1 = R ∧ J / R + 1 = L) := by
  have h1 : J % R < R := Nat.mod_lt _ hR
  have h2 : J / R < L - a + 1 := by
    rw [Nat.div_lt_iff_lt_mul hR]
    have e : (L - a + 1) * R = R * (L - a) + R := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  refine ⟨h1, by omega, ?_⟩
  rintro ⟨e1, e2⟩
  have e3 : J / R = L - a := by omega
  have e4 := Nat.div_add_mod J R
  rw [e3] at e4
  omega

/-- **The geometry of a mask entry**, in the programs' own letters. -/
theorem mask_geometry (cs : Codes) (s : OracleShape) (hR : s.maskRows = 2 ^ ceilLog2 s.maskRows)
    (hA : 1 ≤ s.answers) (J : ℕ)
    (hJ : J < Send.freeMaskEntries s.maskRows (cs.mask.getD s.maskCode default).ell s.answers) :
    J % 2 ^ ceilLog2 s.maskRows < s.maskRows ∧
      J / 2 ^ ceilLog2 s.maskRows < (cs.mask.getD s.maskCode default).ell ∧
      padB cs s true (J % 2 ^ ceilLog2 s.maskRows) (J / 2 ^ ceilLog2 s.maskRows) = false := by
  rw [← hR]
  unfold Send.freeMaskEntries at hJ
  split at hJ
  · exact absurd hJ (Nat.not_lt_zero _)
  · rename_i hc
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at hc
    obtain ⟨h1, h2, h3⟩ := mask_arith s.maskRows (cs.mask.getD s.maskCode default).ell s.answers J
      (Nat.pos_of_ne_zero hc.1) hA hc.2 hJ
    refine ⟨h1, h2, ?_⟩
    cases hb : padB cs s true (J % s.maskRows) (J / s.maskRows) with
    | false => rfl
    | true =>
      exfalso
      unfold padB at hb
      simp only [if_true, Bool.and_eq_true, beq_iff_eq] at hb
      exact h3 hb

/-- **Inside the ranges, off the pad.** -/
theorem mask_inside (cs : Codes) (s : OracleShape) (hR : s.maskRows = 2 ^ ceilLog2 s.maskRows)
    (hA : 1 ≤ s.answers) (J : ℕ)
    (hJ : J < Send.freeMaskEntries s.maskRows (cs.mask.getD s.maskCode default).ell s.answers) :
    InMsg cs s true (J % 2 ^ ceilLog2 s.maskRows) (J / 2 ^ ceilLog2 s.maskRows) ∧
      padB cs s true (J % 2 ^ ceilLog2 s.maskRows) (J / 2 ^ ceilLog2 s.maskRows) = false := by
  obtain ⟨h1, h2, h3⟩ := mask_geometry cs s hR hA J hJ
  refine ⟨?_, h3⟩
  unfold InMsg
  rw [if_pos rfl]
  exact ⟨h1, h2⟩

/-! ## An example and three negative examples -/

/-- One mask code: messages of eight places. -/
def toyMaskCodes : Codes := { base := #[], mask := #[⟨4, 8, 3⟩] }

/-- A message of so many mask rows and answers, without main rows. -/
def toyMask (rows answers : ℕ) : OracleShape :=
  { mainRows := 0, maskRows := rows, maskCode := 0, answers := answers }

theorem mask_met :
    (toyMask 1 1).maskRows = 2 ^ ceilLog2 (toyMask 1 1).maskRows ∧ 1 ≤ (toyMask 1 1).answers ∧
      6 < Send.freeMaskEntries (toyMask 1 1).maskRows
        (toyMaskCodes.mask.getD (toyMask 1 1).maskCode default).ell (toyMask 1 1).answers := by
  decide +kernel

theorem tooth_rows :
    1 ≤ (toyMask 3 1).answers ∧
      3 < Send.freeMaskEntries (toyMask 3 1).maskRows
        (toyMaskCodes.mask.getD (toyMask 3 1).maskCode default).ell (toyMask 3 1).answers ∧
      ¬ 3 % 2 ^ ceilLog2 (toyMask 3 1).maskRows < (toyMask 3 1).maskRows := by
  decide +kernel

theorem tooth_answers :
    (toyMask 1 0).maskRows = 2 ^ ceilLog2 (toyMask 1 0).maskRows ∧
      7 < Send.freeMaskEntries (toyMask 1 0).maskRows
        (toyMaskCodes.mask.getD (toyMask 1 0).maskCode default).ell (toyMask 1 0).answers ∧
      padB toyMaskCodes (toyMask 1 0) true (7 % 2 ^ ceilLog2 (toyMask 1 0).maskRows)
        (7 / 2 ^ ceilLog2 (toyMask 1 0).maskRows) = true := by
  decide +kernel

theorem tooth_free :
    Send.freeMaskEntries (toyMask 1 1).maskRows
        (toyMaskCodes.mask.getD (toyMask 1 1).maskCode default).ell (toyMask 1 1).answers = 7 ∧
      padB toyMaskCodes (toyMask 1 1) true (7 % 2 ^ ceilLog2 (toyMask 1 1).maskRows)
        (7 / 2 ^ ceilLog2 (toyMask 1 1).maskRows) = true := by
  decide +kernel

end Meaning

#print axioms Meaning.mask_arith
#print axioms Meaning.mask_geometry
#print axioms Meaning.mask_inside
#print axioms Meaning.mask_met
#print axioms Meaning.tooth_rows
#print axioms Meaning.tooth_answers
#print axioms Meaning.tooth_free
