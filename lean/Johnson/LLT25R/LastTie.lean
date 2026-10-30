-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastTie.lean: THE TIE BETWEEN TWO NAMES OF THE PROOF FILE's DESCRIPTION: the
last chain's ledger's `FL o mk Z (seatK Z N) N c` (LastSeat.lean, LastRowZeroB.lean) IS
`descN o mk guardedProximityTestParts Z N c` (Johnson/Loose/H2K12/DescN.lean), pulled back along the reading of the
verifier's instance. So what K12's files show of their name (in the goals' scope: `ClosedL` at the
place W, from that description's own test on the plan) reaches the ledger.
  `seatK_is`: the two descriptions' shared seats are one term. `FL_is`: the equation. `planOk_tie`:
    the two descriptions' tests on the plan are one Bool.
Limits. Three equations by unfolding. Nothing on soundness.
-/
import Johnson.LLT25R.LastRowZeroB
import Johnson.Loose.H2K12.DescN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK (sharedN secondN secondN_joined descN)
open ProofFile (SecondHashFunctionArgument LinksBy Cl)
open LPFD.Full (instanceAsPlainRecord)

theorem seatK_is (Z : ProofFile.Pub) (N : H2U.Places4) : seatK Z N = sharedN Z N := rfl

/-- **The ledger's description is K12's files', pulled back.** -/
theorem FL_is (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S Cl) :
    FL o mk Z (seatK Z N) N c = (descN o mk guardedProximityTestParts Z N c).pull instanceAsPlainRecord := by
  unfold descN
  rw [secondN_joined]
  rfl

/-- The two tests on the plan are one. -/
theorem planOk_tie (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S Cl) :
    (FL o mk Z (seatK Z N) N c).planOk = (descN o mk guardedProximityTestParts Z N c).planOk := by
  rw [FL_is]
  rfl

end LLT25

#print axioms LLT25.FL_is
#print axioms LLT25.planOk_tie
