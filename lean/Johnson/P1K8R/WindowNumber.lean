-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WindowNumber.lean: the bound of the format's gate on range checks, in numbers.

The gate's bound at a public part is 2 to the minus (sec + the rounded-up logarithms of the slots,
the batches and the copies). In scope the sizes of a public part that is tied to the public files
are the written ones, so the bound is one number.

  windowBound    the bound at a public part
  written_sum    the exponent at the written sizes is 174: an evaluation in Lean's kernel
  window_number  at public files in scope, under LaidAt, the bound is 2 ^ (-174)

Limits. This file bounds no event. It speaks of a written term alone.
-/
import Johnson.FrontRoad.ParOwnChecks
import E2E.TreeReadsAtFiles

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace P1K8
open OnBytes.Params (clog2)
open OnBytes.FrontRoad (linesAt oneTimeAt columnsFirstAt batchesAt plannedCopies)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifierAndGoals (PublicFiles InScope readFiles)
open OnBytes.Maker (WholeD)
open P5J

/-- **The bound of the format's gate on range checks** at a public part. -/
def windowBound (Zp : ProofFile.Pub) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
    (clog2 (max 1 (batchesAt Zp)) : ℝ) +
    (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ))))

/-- The exponent at the written sizes. -/
theorem written_sum :
    writtenSized.lines.sec + clog2 writtenSized.lines.slots +
        clog2 (max 1 writtenSized.proof.batch.batches) +
        clog2 (plannedCopies writtenSized.lines writtenSized.key.once.shape.fold.columns
          writtenSized.link.shape.columnsFirst) = 174 := by
  decide +kernel

/-- **The bound in numbers**: at public files in scope, under LaidAt. -/
theorem window_number {Z : PublicFiles} (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    windowBound Zp = ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  have hs : Zp.p.chains.made.sized = writtenSized := AtPublicFiles.TreeReads.sized_at scope L
  have hl : linesAt Zp = writtenSized.lines := by
    rw [← OnBytes.FrontRoad.lines_are_frame Z Zp Np cF scope hr L, hs]
  have h₁ : batchesAt Zp = writtenSized.proof.batch.batches := by
    unfold batchesAt
    rw [hs]
  have h₂ : oneTimeAt Zp = writtenSized.key.once.shape.fold.columns := by
    unfold oneTimeAt
    rw [hs]
  have h₃ : columnsFirstAt Zp = writtenSized.link.shape.columnsFirst := by
    unfold columnsFirstAt
    rw [hs]
  have e : (((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
      (clog2 (max 1 (batchesAt Zp)) : ℝ) +
      (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)) = 174 := by
    rw [hl, h₁, h₂, h₃]
    exact_mod_cast written_sum
  unfold windowBound
  rw [e]

end P1K8

#print axioms P1K8.written_sum
#print axioms P1K8.window_number
