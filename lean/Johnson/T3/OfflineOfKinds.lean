-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OfflineOfKinds.lean: the offline clauses of the zero-knowledge statement from the kinds, the rule on the key file's rows unfolded as on the online side.

This file proves zero knowledge of nothing: no value of RowDebtsAt at the key file is given here.
-/
import Johnson.T3.OfflineNamed
import Johnson.T3.OwedOfKindsAt

set_option autoImplicit false
set_option maxRecDepth 20000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides Owed relAt)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open P5J

local instance (priority := high) offlineOfKindsInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) offlineOfKindsInstance2 : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) offlineOfKindsInstance3 : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- **The three offline clauses, from the kinds and the threads at the key file's rows.** -/
theorem offlineClauses_of_kinds (parts : Parts files) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : XF)
        (_ : RowDebtsAt (keyFileDescription d.source d.numbers d.later) parts.book GK
          ((cmKey files).proverAt 0 (parts.prover d))
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true) (_ : AtPublicFiles.Stops.NoSecondStop (parts.prover d)),
        (∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
          ExactOutsideStops (offlineProver parts)
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline.cleared (offlineSimulatorAt d parts GK) ∧
          PrivateStopsAtMost (offlineProver parts)
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline 0 := by
  obtain ⟨d, hd, hc⟩ := offlineClauses_of_live parts scope live
  exact ⟨d, hd, fun GK isProver x₀ debts owns quiet =>
    hc GK isProver x₀ (owed_of_kindsAt debts) owns quiet⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.offlineClauses_of_kinds
