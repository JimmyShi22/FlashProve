-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/SoundAsIOPAtWritten.lean: SOUNDNESS AS AN IOP HAS A MEMBER: at the library's written copy
of the full-size public files, `storedPublicFiles`, WITH NO HYPOTHESIS.

Why. The statements of E2E/SoundAsIOPAtFiles.lean stand under three premises on the public files Z: in
scope, read, and the description's own tests (`protocolDataWellFormed`) pass. If no Z met the three together, they
would be true and say nothing. `premises_zFull` (AtFullSide/Bind/LiveAtNamed.lean) meets them at
`storedPublicFiles`. Here the statements are called there.

  `soundAsIOP_zFull`: sound as an IOP at storedPublicFiles, for every provers.
  `soundAsIOP_protocol_zFull`: the same at the protocol's value `protocolAtFiles storedPublicFiles`.
  `wholeRun_zFull`: the one statement on the whole run at storedPublicFiles: one list of errors, each at most
    2^-128 of its round's challenges, the two rounds in which a point is drawn among them.

Limits. Those of E2E/SoundAsIOPAtFiles.lean. `storedPublicFiles` is a value written in Lean; no theorem ties it to
a file on a disk. That the three premises are met says nothing on whether any prover is accepted: that
is completeness. In the side library, since `theLive_zFull` is an evaluation that is heavy to build.
-/
import E2E.SoundAsIOPAtFilesProofs
import AtFullSide.Bind.LiveAtNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.AtFiles
open Iop Prob Hiop
open AtPublicFiles.AtFiles
open VerifierAndGoals (storedPublicFiles)

/-- **Sound as an IOP at the written full-size files, with no hypothesis**, for every provers. -/
theorem soundAsIOP_zFull (P : (filesAt storedPublicFiles).Provers) : SoundAsIOPAtFiles storedPublicFiles P :=
  let ⟨scope, ⟨pp, read⟩, live⟩ := AtFullSide.Tie.premises_zFull
  soundAsIOPAtFiles storedPublicFiles pp scope read live P

/-- **The same at the protocol's value.** -/
theorem soundAsIOP_protocol_zFull :
    (protocolAtFiles storedPublicFiles).IndexKnowledgeSoundIOP (relationAtFiles storedPublicFiles) (filesAt storedPublicFiles).annT (offlinePlaces storedPublicFiles)
      (filesAt storedPublicFiles).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  let ⟨scope, ⟨pp, read⟩, live⟩ := AtFullSide.Tie.premises_zFull
  soundAsIOPAtTheProtocol storedPublicFiles pp scope read live

/-- **The one statement on the whole run, there.** -/
theorem wholeRun_zFull (P : (filesAt storedPublicFiles).Provers) (fill : ((filesAt storedPublicFiles).withProvers P).Fill) :
    ∃ errors : ((filesAt storedPublicFiles).withProvers P).RoundErrors,
      Err.Below (errors.wholeRun fill) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
        ((filesAt storedPublicFiles).withProvers P).WholeRunSound (relationAtFiles storedPublicFiles) errors fill :=
  let ⟨scope, ⟨pp, read⟩, live⟩ := AtFullSide.Tie.premises_zFull
  wholeRunAtFiles storedPublicFiles pp scope read live P fill

end AtFullSide.AtFiles

#print axioms AtFullSide.AtFiles.soundAsIOP_zFull
#print axioms AtFullSide.AtFiles.soundAsIOP_protocol_zFull
#print axioms AtFullSide.AtFiles.wholeRun_zFull
