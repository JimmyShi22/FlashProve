-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StartWritten.lean: THE TEST startB (Johnson/Top/H0/Fill/D1At.lean: "the request
announces just one message at the chain's start, and its shape is the shape number ix of M") ACCEPTS
AT THE WRITTEN VALUES, BY LEAN's KERNEL; AND SO AT THE COMPOSED MEANING's OWN TERMS, WHERE THE
PUBLIC PART's PLAN IS THE WRITTEN ONE.

Why. The premise hst of r0_paid (Johnson/Road/K4/K04CondPaidB.lean): under it the two texts of "how
many entries the index masks' fresh ledger has" are one number (free0_is,
Johnson/P1L20R/Free0Is.lean).

  `startW sh M ix`: the test's text at a request's shape in the place of the public part.
  `startB_is`: startB Z M ix = startW Z.first.shape M ix. By the definitions.
  `startW_written`: A CLOSED FACT: at shapeFull, mW and nW.indexNo (Johnson/Road/K4/K4PlanTied.lean,
    K4PinsSends.lean, K4PinsBook.lean): true. `startW_written_no`: A NEGATIVE TWIN: at the next
    number: false.
  `startB_at`: under W : WrittenAt Z and hc (the chain's cut is the written one): startB Z
    (msgsOfChain Z.made.proof.1) (P5J.At.N Z cF).indexNo = true.
Limits. W AND hc ARE PREMISES: PAID BY NOBODY HERE. A fact on public values, outside the verifier.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4PinsBook
import Johnson.Road.K4.K4PinsSends
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open VerifiableInference.Desc.First.FillP1 (startB)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.PlanWritten (cutFirstFull)
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- The test's text, at a request's shape. -/
def startW (sh : OnBytes.Params.ReqShape) (M : List OnBytes.OracleShape) (ix : ℕ) : Bool :=
  match M[ix]? with
  | some s => sh.atStart.map (·.shape) == [s]
  | none => false

/-- It is the test. -/
theorem startB_is (Z : ProofFile.Pub) (M : List OnBytes.OracleShape) (ix : ℕ) :
    startB Z M ix = startW Z.first.shape M ix := rfl

/-- **A closed fact: the test accepts at the written values.** -/
theorem startW_written : startW shapeFull mW nW.indexNo = true := by decide +kernel

/-- **A negative twin**: at the next number it rejects. -/
theorem startW_written_no : startW shapeFull mW (nW.indexNo + 1) = false := by decide +kernel

/-- **The test at the composed meaning's own terms**, under W hc. -/
theorem startB_at {Z : ProofFile.Pub} (W : WrittenAt Z)
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    startB Z (msgsOfChain Z.made.proof.1) (P5J.At.N Z cF).indexNo = true := by
  rw [startB_is, (book_of_cut W hc).indexNo, W.shape, W.proof, msgs_sorted]
  exact startW_written

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.startB_is
#print axioms OnBytes.Road.K4.startW_written
#print axioms OnBytes.Road.K4.startW_written_no
#print axioms OnBytes.Road.K4.startB_at
