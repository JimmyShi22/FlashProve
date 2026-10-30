-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/RowsRead.lean: the rows rowA and rowP of Statement.lean ARE what the
two rules of K3Key.lean (rowOfAff, rowOfPlane: "- masks = - value"; turned or not) make of what
maskSide returns, read in the field, part by part: mask form, terms on the planes, target.

Main names:
  readForm_neg: a mask form with every coefficient turned, read.
  rowA_reads: a claim that reads hidden values alone.
  rowP_reads: a claim that reads the planes, turned or not.
  keyF_reads: what a part's key tree leaves, as a claim on the leaves.

Limits. The parts of a row are compared, not a row type of a program: whoever has such a type reads
its three parts. Nothing on how the planes' terms are read into a row of the table.

-/
import Johnson.Desc.First.Look.KeyLaw.MaskSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open Lk6.Mid (RowF)

theorem readForm_neg (m : MaskForm) : readForm (negMasks m) = PscF.scaleForm (-1) (readForm m) := by
  unfold readForm negMasks PscF.scaleForm
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  show (t.1, readE (subE zeroE t.2)) = (t.1, -1 * readE t.2)
  rw [readE_sub, readE_zero]
  congr 1
  ring

variable {F : Fork} {homeA : Array Slot} {home : ℕ → Slot}

/-- A claim that reads hidden values alone: "- masks = - value". -/
theorem rowA_reads (hh : HomeArr homeA home) {a : Aff} {y : MaskForm × E}
    (h : maskSide F homeA a = some y) :
    (⟨readForm (negMasks y.1), [], readE (subE zeroE y.2)⟩ : RowF) = rowA F home a := by
  obtain ⟨h1, h2, -, -⟩ := maskSide_reads hh h
  unfold rowA
  rw [readForm_neg, h1, readE_sub, readE_zero, h2, zero_sub]

/-- A claim that reads the planes. -/
theorem rowP_reads (hh : HomeArr homeA home) {c : PlaneClaim} {y : MaskForm × E}
    (h : maskSide F homeA c.lead = some y) (turned : Bool) :
    (if turned then
        (⟨readForm (negMasks y.1), [(readE c.scalar, pairsF c.pairs)], readE (subE zeroE y.2)⟩ :
            RowF)
      else ⟨readForm y.1, [(readE (subE zeroE c.scalar), pairsF c.pairs)], readE y.2⟩) =
      rowP F home turned c := by
  obtain ⟨h1, h2, -, -⟩ := maskSide_reads hh h
  unfold rowP
  cases turned with
  | true =>
    simp only [if_true]
    rw [readForm_neg, h1, readE_sub, readE_zero, h2, zero_sub]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [h1, h2, readE_sub, readE_zero, zero_sub]

/-- What a part's key tree leaves. -/
theorem keyF_reads (hh : HomeArr homeA home) {k : Array E × Aff} {y : MaskForm × E}
    (h : maskSide F homeA k.2 = some y) :
    readPC ⟨k.1.toList.reverse, y.1, y.2⟩ = keyF F home k := by
  obtain ⟨h1, h2, -, -⟩ := maskSide_reads hh h
  unfold readPC keyF
  rw [h1, h2]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.rowA_reads
#print axioms VerifiableInference.Desc.K3.KeyLaw.rowP_reads
#print axioms VerifiableInference.Desc.K3.KeyLaw.keyF_reads
