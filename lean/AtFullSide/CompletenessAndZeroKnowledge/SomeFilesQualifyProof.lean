-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/SomeFilesQualifyProof.lean: some public files are in use.

1.  WHAT IS CLAIMED: SomeFilesQualify (Johnson/Face/Checks.lean), at the stored full-size files storedPublicFiles: in scope, read, exact match, and they pass the test on
    public files. The two facts: VerifierAndGoals.filesRead.full (Johnson/Goal/Files/FilesReadProof.lean) and AtFullSide.Top.theLive_zFull (AtFullSide/Top/LiveAtFull.lean).
-/
import Johnson.Face.Checks
import AtFullSide.Bind.LiveAtNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation

/-- **Some public files qualify.** -/
theorem someFilesQualify : SomeFilesQualify :=
  let ⟨scope, parameters, read, exact⟩ := VerifierAndGoals.filesRead.full
  ⟨VerifierAndGoals.storedPublicFiles, parameters, { inScope := scope, read := read, exactMatch := exact, pass := AtFullSide.Top.theLive_zFull }⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.someFilesQualify
