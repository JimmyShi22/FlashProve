-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/IndexPlace.lean: code switching, the fifth tie: THE ONE TEST ON THE PLAN
THAT THE FIELD fence OF K2Owes ASKS AT THE CONSTANT (hP of fence_at,
Johnson/Top/H0/K2Ties/AtConstant.lean): IN THE LAID LIST THE INDEX MASKS' TENANT STANDS AT ITS OWN
NUMBER: where the constant's parameters are the written values. NO SUB-PROTOCOL IMPORTS THIS FILE.
  codes_of_sends   the sized proof's written codes are the written sendings' own:
                  Second.Seam.codes_written (Johnson/Second/Seam/CodesOneInScope.lean), under the
                  name by which files of this folder and of Johnson/P1K2R/ call it
  index_written   THE CLOSED FACT: in the written tenants' list the index masks' tenant stands at
                  the number that the written cut tells: by Lean's kernel
  index_beside    a negative test: at the next number another tenant stands
  hP_at           THE STATEMENT, at the constant's letters
CALLED: AtWritten (K2Ties/WrittenAt.lean) · AtTold (K2Ties/ToldAt.lean) · places_at
(Johnson/Top/H0/K2Caller/PlacesWritten.lean).
LIMITS. The full size alone. AtWritten and AtTold stand under the two pinned tests' accepts; «the
first proof chain's sendings are the written ones» is a premise here (other files have it under
the first of them). No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.ToldAt
import Johnson.Top.H0.K2Caller.PlacesWritten
import Johnson.P5J.LettersAt2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open Johnson.G (proofSends0)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (msgNoOf)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open VerifiableInference.PlanWritten (proofSizedFull)
open P1Named (tenantsFull places_at)
open P5J (TS)

theorem codes_of_sends : proofSizedFull.codes = proofSends0.codes := Second.Seam.codes_written

/-- **The closed fact.** -/
theorem index_written :
    tenantsFull[msgNoOf toldFull P5T.N0Full.index]? = some P5T.N0Full.index := by decide +kernel

theorem index_beside :
    decide (tenantsFull[msgNoOf toldFull P5T.N0Full.index + 1]? = some P5T.N0Full.index) =
      false := by decide +kernel

/-- **In the laid list the index masks' tenant stands at its own number.** -/
theorem hP_at {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) (T : AtTold Zp cF)
    (hs : Zp.made.proof.1 = proofSends0) {L : Laid} (hl : P5J.At.laid? Zp = some L) :
    L.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index := by
  have hc : Zp.first.codes = proofSends0.codes := by
    show P5J.At.cs Zp = _
    rw [A.cs, codes_of_sends]
  have hl' : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L := hl
  have hp : P5T.planSeats Zp Zp.D.1 = P5T.psFull := A.pseats
  rw [T.indexNo, A.index, places_at hc hs hp hl', hp]
  exact index_written

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.codes_of_sends
#print axioms VerifiableInference.Desc.First.K2Ties.index_written
#print axioms VerifiableInference.Desc.First.K2Ties.index_beside
#print axioms VerifiableInference.Desc.First.K2Ties.hP_at
