-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/StoredAtTheBase.lean: the base prover has every stored column that the description declares, at the table
coins that the honest online prover reads: the field stored of TheSockets (AtFullSide/Honest/TheOneObject.lean).

  1  online_of_base      where the base maker returns A, the online maker returns A read through
  2  stored_at_the_base  at every index i and every randomness ri of the object: every stored table that a round of the
                         description declares has, at every position below its depth, a column of the declared width in
                         A.H at (i, tableCoins files ri)

2 is stored_at_the_maker (AtFullSide/Honest/StoredAtReturn.lean) at the return of 1; the columns of a prover read through
are the prover's (storedWords_thru, Honest/ThruRun.lean: by definition). It reads no request and no tie: the socket asks it
under TiedX; it holds at every input.

Limits. made (the base maker returns), the head h, scope and live are hypotheses. It says that a column of the declared
width is there, not what it holds. This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.Honest.StoredAtReturn
import Johnson.Desc.ProofFile.Honest.ThruAtPure
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput tableCoins baseMaker onlineMaker)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **Where the base maker returns A, the online maker returns A read through.** -/
theorem online_of_base (made : baseMaker files = .ok A) :
    onlineMaker files = .ok (A.thru id (tableCoins files) matrixInput.dummy) := by
  obtain ⟨-, -, -, -, hd⟩ := atPure_tests made
  obtain ⟨e₁, e₂⟩ := inRange_of_atPure made
  rw [e₁, e₂] at hd
  exact atPure_through id (tableCoins files) matrixInput.dummy made hd

/-- **The field stored, at every input.** -/
theorem stored_at_the_base (h : HeadAtReturn files A) (made : baseMaker files = .ok A)
    (scope : VerifierAndGoals.InScope files = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (i : FullSizeMatrix) (ri : (protocolAtFiles files).EncodingRandomness) :
    ∀ d ∈ h.description.roundsDeclaredByBlocks.1 ++ h.description.roundsDeclaredByBlocks.2.1 ++ h.description.roundsDeclaredByBlocks.2.2,
      ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
        ∃ u, A.H.storedWords i (tableCoins files ri) t.item y = some u ∧ u.length = t.sh.W :=
  AtPublicFiles.AtFiles.HonestTerm.stored_at_the_maker (A.thru id (tableCoins files) matrixInput.dummy)
    (online_of_base made) h.places h.firstChain scope live h.head.laid i ri

end AtFullSide.Honest

#print axioms AtFullSide.Honest.online_of_base
#print axioms AtFullSide.Honest.stored_at_the_base
