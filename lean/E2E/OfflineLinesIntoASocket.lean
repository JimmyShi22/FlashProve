-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineLinesIntoASocket.lean: THE THREE OFFLINE LINES, HANDED TO WHOEVER ASKS THEM AS PREMISES. A law that takes, at arguments `parts` of the
honest provers and a simulator that is a letter, the three offline lines as premises, holds at `thePartsAt Z`.

  `offline_lines_into_a_socket`   for every C : Parts Z → Prop:
                                  (∀ parts offlineSimulator, offlineTable → offline → offlineStops → C parts) → C (thePartsAt Z)

The three premises: the committed table is the object's encoding; `ExactOutsideStops` at the cleared offline work; `PrivateStopsAtMost` at the
offline work, 0. Their text is meant to be that in which zero knowledge on served requests asks them of the offline prover; THAT LAW IS NOT
IMPORTED HERE: that the terms are the same Lean judges only where such a law is handed in as `socket`. The simulator that is handed in: `offlineSimulatorAt d (thePartsAt Z) (rowsAtTheTerm d (theSimulators d) (theLetters d))`.

Limits. It says of no C that it is zero knowledge, and it calls no law on the online prover or the link. What stands behind the
three lines: E2E/OfflineClausesAtTheFiles.lean, whose limits stand.
-/
import E2E.OfflineClausesAtTheFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) linesIntoASocketPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) linesIntoASocketValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) linesIntoASocketDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles}

/-- **Whoever asks the three offline lines as premises has them at the named value.** -/
theorem offline_lines_into_a_socket (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (scope : InScope Z = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {C : Parts Z → Prop}
    (socket : ∀ (parts : Parts Z) (offlineSimulator : Compile.Lifetime.SimOf (protocolAtFiles Z).offline)
      (_offlineTable : ∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
      (_offline : ExactOutsideStops (offlineProver parts)
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared
        offlineSimulator)
      (_offlineStops : PrivateStopsAtMost (offlineProver parts)
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline 0), C parts) :
    C (thePartsAt Z) := by
  obtain ⟨d, -, -, -, h1, h2, h3⟩ := offline_clauses_at_the_files live scope hr
  exact socket (thePartsAt Z) _ h1 h2 h3

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offline_lines_into_a_socket
