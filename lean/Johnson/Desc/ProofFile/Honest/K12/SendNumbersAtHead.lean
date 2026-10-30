-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SendNumbersAtHead.lean

Eight numbers of the shared chain's two sendings' jobs (`jobU`, `jobOmega`:
Honest/K14/Sendings.lean), at the shared chain's own plan, under the head: where three messages'
coins begin among their senders' coins, how many they are, and that each sender takes at least so
many. One definition with code; five theorems.

  `sendNumbersB`: the test.
  `sendNumbersB_plan`: it reads of the public data the codes and the shape alone.
  `sendNumbers_of`: where it accepts, the eight hold.
  `sendNumbers_real`: it accepts at the typed sizes over a proof file's own codes: an evaluation in
      Lean's kernel.
  `sendNumbers_bite`: it can fail: at the key file's typed sizes it says no: an evaluation in Lean's
      kernel.
  `sendNumbers_head`: it accepts at the plan under the head.

What for. `bookCutsU_at_laid` (AtFullSide/K12/CutsAtLaid.lean, in the side library) takes the eight
as premises on the public data; `he_at_laid` (there) takes none of them and has one of these
numbers, 42853, in its conclusion.

By what. The pattern of FitAtHead.lean: `written_at_head`, `qAt_written`, `planOf`.

Beside it. The shared rounds' authors have four of the eight numbers in other letters, at the
library's written plan: `numbers_tie` (Honest/K14/SharedAheadOwners.lean: 42853, 216, 10808, 167, of
their spFirstCoin, maskFirstCoin and maskRun), `headNumbers_written`
(Honest/K14/BookAtOmegaHead.lean), `uNumbers_written` (Honest/K14/BookAtUHead.lean). At this plan
they have two tests of their own that name no number, at one earlier hash (`numbers_at_files`,
`uNumbers_at_files`, there). Here: the eight as numbers, in the letters of `offsetOf`, `dueOf` and
`takesOf`, at this plan, under the head at any earlier hash.

Limits.
- The numbers are written by hand, off the library's written list of the book's entries. The full
  size alone.
- `sendNumbers_real` is a sentence on all values of an optional value: by itself it would hold for
  nothing if the typed sizes were none. That they are there the library has with no premise
  (`real_members`, Johnson/Desc/K1/Law/CondReal.lean); no theorem of this file calls it:
  `sendNumbers_head` has it from `written_at_head`.
- The control shows that the test parts two typed plans of the library's; it does not show which of
  the eight says no there, nor that each can.
- At the number 0 of "LIN point" alone (by `sendNumbersB_plan` the test does not read that number).
- Public data alone: no coin, no run. It moves no count. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open Lk6.AtPlan (keyFull)
open ProofFile.Honest.K14 (SendPub jobU jobOmega offsetOf dueOf takesOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **A test with code on eight numbers of the two sendings' jobs**: where each of three messages'
coins begin among its sender's coins and how many they are (o_u; o_sp; the first mask), and that
each sender takes at least so many coins of the extension field. The numbers are those of the three
entries by which the second part of the test on G_u carries at the library's written list of the
book's entries (AtFullSide/K12/CutsAtLaid.lean). -/
def sendNumbersB (A : SendPub) : Bool :=
  (offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 0 == 0) &&
  (dueOf (jobU A).Q.codes (shapeAt (jobU A) 0) ((jobU A).sort 0) == 10808) &&
  (offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 == 42853) &&
  (dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) == 216) &&
  (offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1 == 10808) &&
  (dueOf (jobU A).Q.codes (shapeAt (jobU A) 1) ((jobU A).sort 1) == 167) &&
  decide (10975 ≤ (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).e) &&
  decide (43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e)

/-- The test reads of the public data the codes and the shape alone. -/
theorem sendNumbersB_plan (A : SendPub) :
    sendNumbersB A = sendNumbersB (planOf A.P.codes A.P.S) := rfl

/-- Where the test accepts, the eight hold: in the letters of the eight premises of
`bookCutsU_at_laid` (AtFullSide/K12/CutsAtLaid.lean). -/
theorem sendNumbers_of (A : SendPub) (h : sendNumbersB A = true) :
    offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 0 = 0 ∧
    dueOf (jobU A).Q.codes (shapeAt (jobU A) 0) ((jobU A).sort 0) = 10808 ∧
    offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 = 42853 ∧
    dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) = 216 ∧
    offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1 = 10808 ∧
    dueOf (jobU A).Q.codes (shapeAt (jobU A) 1) ((jobU A).sort 1) = 167 ∧
    10975 ≤ (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).e ∧
    43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e := by
  unfold sendNumbersB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- It accepts at the typed sizes over a proof file's own codes. An evaluation in Lean's kernel. -/
theorem sendNumbers_real :
    (realSized.all fun q => sendNumbersB (planOf q.2 q.1.shape)) = true := by decide +kernel

/-- It can fail: at the key file's typed sizes it says no. An evaluation in Lean's kernel. -/
theorem sendNumbers_bite : sendNumbersB (planOf keyFull.codes keyFull.once.shape) = false := by
  decide +kernel

/-- **The test accepts at the shared chain's own plan, under the head.** -/
theorem sendNumbers_head (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    sendNumbersB ⟨K1.qAt Zp Np, 0⟩ = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := sendNumbers_real
  rw [hx] at k
  have k' : sendNumbersB (planOf codesFull2 x.shape) = true := k
  rw [sendNumbersB_plan, qAt_written Wr Np]
  exact k'

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.sendNumbersB
#print axioms ProofFile.Honest.K12.Light.sendNumbersB_plan
#print axioms ProofFile.Honest.K12.Light.sendNumbers_of
#print axioms ProofFile.Honest.K12.Light.sendNumbers_real
#print axioms ProofFile.Honest.K12.Light.sendNumbers_bite
#print axioms ProofFile.Honest.K12.Light.sendNumbers_head
