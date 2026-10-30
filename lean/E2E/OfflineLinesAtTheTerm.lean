-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineLinesAtTheTerm.lean: the three offline lines of zero knowledge, CARRIED FROM THE ARGUMENTS AT A DESCRIPTION
(`partsOfDescription d`) TO THE NAMED VALUE (`thePartsAt files`, E2E/KeyArgumentsAt.lean), where the public files make the
description d.

  `offlineProver_at_the_term`     the two offline provers are one
  `offlineSimulator_at_the_term`  the two offline simulators are one: over `rowsAtTheTerm d S c`
                                  (E2E/OfflineObjectAtTheTerm.lean) and over `offlineRowsAt d offlineProverCoinCounts S c`
  `lines_at_the_term`             the three lines at the one give the three lines at the other

Equations between terms, and a rewriting. Nothing says that the three lines hold. Nothing on any property.
-/
import E2E.OfflineObjectAtTheTerm
import E2E.OfflineRowsJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)

local instance (priority := high) linesAtTheTermValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) linesAtTheTermDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles} {d : OfflineDescription}

/-- **The two offline provers are one.** -/
theorem offlineProver_at_the_term (hd : offlineDescription files = .ok d) :
    offlineProver (thePartsAt files) = offlineProver (partsOfDescription (files := files) d) :=
  congrArg offlineProver (thePartsAt_ok hd)

/-- **The two offline simulators are one.** -/
theorem offlineSimulator_at_the_term (hd : offlineDescription files = .ok d)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    offlineSimulatorAt d (thePartsAt files) (rowsAtTheTerm (files := files) d S c) =
      offlineSimulatorAt d (partsOfDescription (files := files) d)
        (offlineRowsAt (files := files) d offlineProverCoinCounts S c) := by
  show simKey files (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts runValueBytes runValueBytes
      (offlineStart d) (offlineRowsAt (files := files) d offlineProverCoinCounts S c)
      ((thePartsAt files).prover d) (offlineRowsAt (files := files) d offlineProverCoinCounts S c).sims = _
  rw [object_prover hd]
  rfl

/-- **The three lines at the arguments at the description give the three lines at the named value.** -/
theorem lines_at_the_term (hd : offlineDescription files = .ok d) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit)
    (h : (∀ i r e, (offlineProver (partsOfDescription (files := files) d)).ext (i, r, e) =
        (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
        (offlineSimulatorAt d (partsOfDescription (files := files) d)
          (offlineRowsAt (files := files) d offlineProverCoinCounts S c)) ∧
      PrivateStopsAtMost (offlineProver (partsOfDescription (files := files) d))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0) :
    (∀ i r e, (offlineProver (thePartsAt files)).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver (thePartsAt files))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
        (offlineSimulatorAt d (thePartsAt files) (rowsAtTheTerm (files := files) d S c)) ∧
      PrivateStopsAtMost (offlineProver (thePartsAt files))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 := by
  rw [offlineProver_at_the_term hd, offlineSimulator_at_the_term hd S c]
  exact h

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offlineProver_at_the_term
#print axioms AtPublicFiles.OfflineRows.offlineSimulator_at_the_term
#print axioms AtPublicFiles.OfflineRows.lines_at_the_term
