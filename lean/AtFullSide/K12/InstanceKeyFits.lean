-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/InstanceKeyFits.lean: at the shared thread at the base prover the key of a valid input
has the planned sizes, where the chain's input's key is the committer's.

  key_fits_term   the statement: the premise hk of stand_twelve_at_ready.

By what: fiveFieldsK14_inScope, field key. NOT IN FRONT OF A LAW OVER COINS (the rule:
Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The ground: hw ties the letter w's key to its coins
(the first kind); key_at_base lifts it at an instance written of the object's record.
-/
import AtFullSide.K12.InstanceTerm
import AtFullSide.K14.AtLaidLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.Own (keyFits)
open ProofFile.Honest.FirstThread

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The key has its planned sizes, at every valid input of the thread.** -/
theorem key_fits_term (h : HeadAtReturn files A) (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (reads : IndexReaders FullSizeMatrix IndexCommitterCoins) (parts : SharedThreadParts A WtShared)
    (w : Common FullSizeMatrix IndexCommitterCoins TableKey) (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (v : Common FullSizeMatrix IndexCommitterCoins TableKey) (hv : (sharedThread h reads parts w).valid v) :
    keyFits v.key (K1.qAt A.Z h.places).par.S.fold.index = true := by
  obtain ⟨rfl, hr⟩ := hv
  exact (Bind.ForProver.fiveFieldsK14_inScope scope (ProofFile.Honest.K5.parts_of_atPure base).1.pub
    (Desc.K14.beforePointOf h.places)).key ⟨matrixInput.weights A.Z v.w₀, v.rc, v.key⟩ (hw hr)

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.key_fits_term
