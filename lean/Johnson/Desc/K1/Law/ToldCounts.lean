-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ToldCounts.lean: WHAT A SENDING OF KIND K1 TELLS, COUNTED: where the place's trees can be laid, the block's field "oracles" (Johnson/Desc/K1/Send.lean) tells as many trees as the
layout has and, under them, as many tenants as the place sends messages. Two calls: K1.oracles_declares (Johnson/Desc/K1/Law/Declares.lean) and declaredCounts (Johnson/Desc/K1/Law/SentAtProofs.lean).
ASKED for the third count of the promise's clause on the book (bookAt).
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.SentAtProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes

theorem told_counts (P : Par) (h : Own.treesCan P.codes P.sent = true) :
    (oracles P).flatten.length = (layOf P).shapes.size ∧
      ((oracles P).flatten.map fun o => o.tenants.length).sum = P.sent.size := by
  rw [Own.treesCan_eq] at h
  obtain ⟨lay, hl⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨decl, e, hD⟩ := oracles_declares P lay hl
  have e2 : (oracles P).flatten = decl := by rw [e]; simp
  have e3 : layOf P = lay := by unfold layOf; rw [hl]; rfl
  rw [e2, e3]
  exact ⟨hD.trees, declaredCounts decl lay _ _ hD⟩

/-- In the asker's letters: under the kind's own test on the plan. -/
theorem told_tenants (P : Par) (h : planOk P = true) :
    ((oracles P).flatten.map fun o => o.tenants.length).sum = P.sent.size := by
  unfold planOk at h
  simp only [Bool.and_eq_true] at h
  exact (told_counts P h.1.2).2

/-- **The asker's sentence, to the letter.** -/
theorem told_tenants_own (P : Par) (h : planOkOwn P = true) :
    ((oracles P).flatten.map fun o => o.tenants.length).sum = P.sent.size := by
  unfold planOkOwn at h
  exact told_tenants P (Bool.and_eq_true_iff.1 h).1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.told_counts
#print axioms VerifiableInference.Desc.K1.told_tenants
#print axioms VerifiableInference.Desc.K1.told_tenants_own
