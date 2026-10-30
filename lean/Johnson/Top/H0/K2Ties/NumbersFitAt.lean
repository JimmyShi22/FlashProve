-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/NumbersFitAt.lean: code switching: THE TEST ON THE PLAN's NUMBERS numbersFit
(Johnson/Desc/First/Borders.lean) ACCEPTS AT THE CONSTANT's OWN NUMBERS: where the constant's
parameters are the written values. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. Two payers of the code switch's ties take «numbersFit os N n = true» at some list os of oracle
messages (index_off_switch, K2Ties/KeptOff.lean; k02_t4R_hE, TieFourPadsAt.lean). It is a clause of
the one test on the table's letters (planSideOk), which nobody holds at the constant's letters.
  numbersFit_congr     the test reads of the numbers six letters alone: sent · index · w · inside ·
                       keptOf · group
  numbersFit_written   THE CLOSED FACT: at the written numbers and what the written cut tells the
                       test accepts: by Lean's kernel
  numbersFit_bent      a negative test: with the index masks' tenant laid in W's place it rejects
  numbersFit_at        THE STATEMENT, at the constant's numbers
CALLED: AtWritten (K2Ties/WrittenAt.lean) · toldFull (K2Ties/ToldAt.lean).
LIMITS. The full size alone. AtWritten stands under the first pinned test's accept. The list of
oracle messages is the WRITTEN cut's: that it is what the seated sub-protocols tell is not said here
(AtTold has it under the cut's pinned test); the two payers ask no such thing. No soundness is
claimed.
-/
import Johnson.Top.H0.K2Ties.ToldAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain Oracle)
open VerifiableInference.Desc.First (Numbers numbersFit)
open P5J (TS)

theorem numbersFit_congr {os : List Oracle} {N N' : Numbers} {n : ℕ} (hs : N.sent = N'.sent)
    (hi : N.index = N'.index) (hw : N.w = N'.w) (hin : N.inside = N'.inside)
    (hk : N.keptOf = N'.keptOf) (hg : ∀ l, N.group l = N'.group l) :
    numbersFit os N n = numbersFit os N' n := by
  unfold numbersFit
  simp only [hs, hi, hw, hin, hk, hg]

/-- **The closed fact.** -/
theorem numbersFit_written : numbersFit toldFull.flatten P5T.N0Full 25 = true := by
  decide +kernel

theorem numbersFit_bent :
    numbersFit toldFull.flatten { P5T.N0Full with w := P5T.N0Full.index } 25 = false := by
  decide +kernel

/-- **The test accepts at the constant's own numbers.** -/
theorem numbersFit_at {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) :
    numbersFit toldFull.flatten (P5J.At.N Zp cF) 25 = true := by
  rw [numbersFit_congr A.sent A.index A.w A.inside A.keptOf A.group]
  exact numbersFit_written

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.numbersFit_congr
#print axioms VerifiableInference.Desc.First.K2Ties.numbersFit_written
#print axioms VerifiableInference.Desc.First.K2Ties.numbersFit_bent
#print axioms VerifiableInference.Desc.First.K2Ties.numbersFit_at
