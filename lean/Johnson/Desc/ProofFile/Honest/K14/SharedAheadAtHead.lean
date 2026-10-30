-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SharedAheadAtHead.lean: IN THE GOALS' SCOPE AND UNDER THE
LIBRARY's LaidAt (Johnson/P5J/LaidOpens.lean) THE FRAME's sharedAhead (Honest/BookShared.lean)
RETURNS AT THE PROOF FILE's OWN DESCRIPTION AND THE WRITTEN LIST OF THE SHARED CHAIN's SENDINGS, AND
WHAT IT RETURNS IS THE WRITTEN LIST OF FOURTEEN ENTRIES (writtenShort,
Honest/K14/SharedAheadWritten.lean). Two statements, each with its proof: calls alone.

  sharedAhead_at_laid   **sharedAhead (F0T o Zp Np cF) proofSendsFull.2.1 = .ok writtenShort**: the
                  return at the written description (sharedAhead_written), carried by
                  sharedAhead_carried (Honest/BookSharedAlike.lean) along planAlike_at_laid
                  (Honest/K14/WrittenAtHead.lean)
  sharedAhead_at_head   the same under the library's head

Limits. The full size alone. THAT ANY FILES MEET LaidAt IS NOT SHOWN HERE. It says that sharedAhead
returns and what; NOT that a book's own tests pass, nor that the whole book's maker returns:
sharedAhead is a second text of a part of two definitions of the frame's, and no maker of a book
calls it. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SharedAheadWritten
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.BookSharedAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open Johnson.G (proofSendsFull)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **IN SCOPE, UNDER LaidAt, THE FRAME's sharedAhead RETURNS THE WRITTEN LIST AT THE
DESCRIPTION.** -/
theorem sharedAhead_at_laid (scope : InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    sharedAhead (F0T o Zp Np cF) proofSendsFull.2.1 = .ok writtenShort :=
  sharedAhead_carried (planAlike_at_laid scope L) sharedAhead_written

/-- **The same under the library's head.** -/
theorem sharedAhead_at_head {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    sharedAhead (F0T o Zp Np cF) proofSendsFull.2.1 = .ok writtenShort :=
  sharedAhead_at_laid h.scope h.laid

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sharedAhead_at_laid
#print axioms ProofFile.Honest.K14.sharedAhead_at_head
