-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/TreesWritten.lean: the number of trees that the first chain sends, by the data at
the written lists of rounds (`writtenPFull.t₁`, Johnson/Flat/Dec/FitAtWritten.lean), is 83; and the
premises hI and hV of the law on the shared chain against that closed term. Statements
with their proofs.

Why it is no evaluation over all rounds. `WholeD.t₁` (OnBytes/Maker/Whole.lean) adds up, round by
round, how many trees a round sends: a sum over 48,292 rounds, which Lean's kernel does not bear.
That sum is the length of the list of all trees (`List.length_flatMap`), and the library has that
list as a written value already, by an evaluation that the kernel bore: `trees1_proofFull`
(Johnson/G/DryProofTestsFull.lean). Its length is a small closed fact.

  `t1_written`: 83. `t2_written`: the shared chain: 11.
  `hI_hV_t1`: (W) at the core of the numbers at the written values.
  `hI_hV_t1_in_scope`: (Z) in the goals' scope, at the public part's own numbers. With the
    theorem that the IOP as written in Lean at the seat tells `writtenPFull.t₁` trees (in
    scope, where the value is laid) these are the binders; that theorem is not called here.
The negative test: `hV_rejects` (Johnson/HB/LLHARD/IdxBelowWritten.lean): at 82 W's fails.

Limits. Nothing on soundness.
-/
import Johnson.Flat.Dec.FitAtWritten
import Johnson.HB.LLHARD.IdxBelowWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Maker

/-- **The data at the written lists of rounds say that the first chain sends 83 trees.** -/
theorem t1_written : writtenPFull.t₁ = 83 := by
  have e : ((WholeD.of 32 wProofFull).ds₁.flatMap (·.trees)).length = 83 := by
    rw [trees1_proofFull]
    decide
  rw [List.length_flatMap] at e
  rw [writtenPFull_eq]
  exact e

/-- And the shared chain 11. -/
theorem t2_written : writtenPFull.t₂ = 11 := by
  have e : ((WholeD.of 32 wProofFull).ds₂.flatMap (·.trees)).length = 11 := by
    rw [trees2_proofFull]
    decide
  rw [List.length_flatMap] at e
  rw [writtenPFull_eq]
  exact e

/-- **hI and hV against that closed term**, at the written values. -/
theorem hI_hV_t1 : P5T.N0Full.index.1 < writtenPFull.t₁ ∧ P5T.N0Full.w.1 < writtenPFull.t₁ := by
  rw [t1_written]
  exact ⟨VerifiableInference.Desc.K13.Law.hI_written, VerifiableInference.Desc.K13.Law.hV_written⟩

/-- The same in the goals' scope, at the public part's own numbers. -/
theorem hI_hV_t1_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : WholeD}
    {r : LPFD.Full.RunPF} (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made =
      true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    (P5T.numbersOf (P5T.planSeats Z Z.D.1)).index.1 < writtenPFull.t₁ ∧
      (P5T.numbersOf (P5T.planSeats Z Z.D.1)).w.1 < writtenPFull.t₁ := by
  rw [t1_written]
  exact VerifiableInference.Desc.K13.Law.hI_hV_in_scope hW h hy hl

end Johnson.G

#print axioms Johnson.G.t1_written
#print axioms Johnson.G.t2_written
#print axioms Johnson.G.hI_hV_t1
#print axioms Johnson.G.hI_hV_t1_in_scope
