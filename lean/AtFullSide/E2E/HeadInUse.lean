-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/HeadInUse.lean

This file proves that, at all public files in use, the function onlineProverFromPublicFiles returns a value at
matrixFilling and a record HeadAtReturn exists at that value. Theorems stated "for every returned
value A with a record HeadAtReturn files A" therefore apply at all public files in use.

Terms.
  * Public files are "in use" when FilesInUse files parameters holds
    (Johnson/Face/FinalStatement.lean): the files are in scope (InScope), they read as these
    parameters, their policy is exact match, and they pass protocolDataWellFormed, the verifier's first test on
    public files. FilesInUse is the condition on files in the top statements on completeness and
    zero knowledge.
  * onlineProverFromPublicFiles (Johnson/Desc/ProofFile/Honest/AtPure.lean) is the function that builds the honest
    prover's data (the structure OnlineProverWithDescription) from the bytes of the public files and an argument, here
    matrixFilling. It can fail.
  * HeadAtReturn files A (Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) is a record:
    the data from which the online proof's description is made at A, and (its field head) the
    library's facts on the public part of A, among them that the files are in scope.

Main statements.
  * head_in_use: at all public files in use there are a value A and a record of type HeadAtReturn
    files A such that onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A.

Limits.
  * This is neither completeness nor zero knowledge, and it says nothing about the messages that
    the returned prover sends. It says only that a returned value and a record at it exist.
  * The proof only combines two theorems of other files.
  * Of FilesInUse, the proof uses the fields inScope and pass alone.
  * The statement holds for the full-size layout alone (InScope: the layout file is that of the
    stored full-size example), and for the format's second hash function OnBytes.secondHashFunction alone.

Built on.
  * base_returns (AtFullSide/K1/SimAtTermAll.lean): in scope and under protocolDataWellFormed, onlineProverFromPublicFiles returns a
    value at baseFilling, which in that file abbreviates the same term as matrixFilling
    (E2E/ThruAtTerm.lean).
  * headAtReturn_base (AtFullSide/K1/HeadAtReturn.lean): a record HeadAtReturn exists at that
    value.
  * FilesInUse (Johnson/Face/FinalStatement.lean).
-/
import Johnson.Face.FinalStatement
import AtFullSide.K1.SimAtTermAll
import AtFullSide.K1.HeadAtReturn
import E2E.ThruAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open ProofFile.Honest (onlineProverFromPublicFiles openHonest)
open ProofFile.Honest.Term (matrixInput matrixFilling)

/-- At all public files in use, onlineProverFromPublicFiles returns a value at matrixFilling, and a record HeadAtReturn
exists at that value. -/
theorem head_in_use : ∀ files parameters (inUse : FilesInUse files parameters),
    ∃ (A : ProofFile.Honest.OnlineProverWithDescription AtPublicFiles.AtFiles.FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Honest.Cells Unit Unit)
      (_ : ProofFile.Honest.FirstThread.HeadAtReturn files A),
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A := by
  intro files parameters inUse
  obtain ⟨A, made⟩ := AtFullSide.K1.base_returns files inUse.inScope inUse.pass
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_base files matrixInput OnBytes.HonestTrace.Sz.ref
    openHonest inUse.inScope inUse.pass made
  exact ⟨A, h, made⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.head_in_use
