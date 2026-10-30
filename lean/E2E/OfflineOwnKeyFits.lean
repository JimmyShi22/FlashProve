-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnKeyFits.lean: AN INSTANCE THAT IS WRITTEN OF AN OOD SAMPLE HAS A KEY OF THE WRITTEN SIZES (`keyFits`,
Johnson/Desc/Own/KeyTests.lean, at the written plan's index shape): so has every instance in a relation `relAt`
(Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) whose writing map writes `keyInstanceOfOutOfDomainSample` of the sample. This is the premise hkey of
E2E/OfflineOwnFolds.lean's `asks_reached` and of what stands on it.

  `index_written`          the written index shape's three numbers: a kernel line
  `keyFits_written`        at `keyInstanceOfOutOfDomainSample rec`, at every sample
  `keyFits_of_relation`    at every instance in the relation

Limits. On the key's sizes alone: nothing on what the key holds. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.TiedAtFiles
import E2E.KeyShapeSharedTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS)
open ProofFile.Honest (relAt)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (Xi keyInstanceOfOutOfDomainSample)
open AtPublicFiles.AtFiles.Full (QK)

/-- The written index shape's three numbers. -/
theorem index_written : QK.par.S.fold.index.v = frS.P.v ∧ QK.par.S.fold.index.answers = 1 ∧
    QK.par.S.fold.index.cubeBits = 29 := by decide +kernel

/-- **The key written of a sample has the written sizes.** -/
theorem keyFits_written (rec : RecFull) : keyFits (keyInstanceOfOutOfDomainSample rec).key QK.par.S.fold.index = true :=
  AtPublicFiles.Committed.key_fits rec _ index_written.1 index_written.2.1 index_written.2.2

/-- **So has every instance in the relation.** -/
theorem keyFits_of_relation {I X RI Seed Ans : Type} (ans : I → RI → Seed → Ans) (Ryes : I → X → Prop)
    (wr : X × (Seed × Ans) → Xi) (hwr : ∀ a, ∃ rec : RecFull, wr a = keyInstanceOfOutOfDomainSample rec) {i : I} {r : RI}
    {x : Xi} (h : relAt ans Ryes wr i r x) : keyFits x.key QK.par.S.fold.index = true := by
  obtain ⟨s, x', e, -⟩ := h
  obtain ⟨rec, hrec⟩ := hwr (x', (s, ans i r s))
  rw [e, hrec]
  exact keyFits_written rec

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.index_written
#print axioms AtPublicFiles.OfflineRows.keyFits_written
#print axioms AtPublicFiles.OfflineRows.keyFits_of_relation
