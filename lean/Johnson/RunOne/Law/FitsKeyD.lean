-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FitsKeyD.lean: Fits
(SeatsKeyD.lean) FROM FOUR PLAIN FACTS: the statement has the own message's main table; it has the
index-mask message; what the two ledgers hand out lies inside the two messages' mask tables.

Main names:
  homesFrom_mem: every home is one of the entries handed in.
  fits_of_lists: Fits.

Limits. The four facts are premises.

-/
import Johnson.RunOne.Law.SeatsKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FitsKeyD
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open Johnson.RunOne.Law.SeatsKeyD

/-- Every home is one of the entries handed in. -/
theorem homesFrom_mem : ∀ (bs : List Bool) (o k : List Slot) (s : Slot), s ∈ homesFrom bs o k →
    s ∈ o ∨ s ∈ k
  | [], _, _, _, h => by cases h
  | false :: bs, [], k, s, h => by cases h
  | false :: bs, a :: o, k, s, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases homesFrom_mem bs o k s h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
  | true :: bs, o, [], s, h => by
    cases o <;> cases h
  | true :: bs, o, a :: k, s, h => by
    have h' : s ∈ a :: homesFrom bs o k := by
      cases o <;> exact h
    rcases List.mem_cons.1 h' with rfl | h'
    · exact Or.inr List.mem_cons_self
    · rcases homesFrom_mem bs o k s h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- **Fits, from four plain facts.** -/
theorem fits_of_lists {one : OneTime} {id : ℕ} {m : Wf.Matrix} {l : WfLookup} {oL kL : List ℕ}
    {idxN : ℕ} {S : Statement} (hT : TablesFit S one.ranges one.codes)
    (hi : idxN < S.oracles.size)
    (ho : ∀ j ∈ oL, j < Means.tableSize S one.ranges.messageId .mask)
    (hk : ∀ j ∈ kL, j < Means.tableSize S idxN .mask) : Fits one id m l oL kL idxN S := by
  refine ⟨hT, fun s hs => ?_⟩
  have hs' : s ∈ homesFrom (fromKeys (faceOfLkp (Wf.lookupOf id m l)))
      (oL.map fun j => ⟨one.ranges.messageId, j⟩) (kL.map fun j => ⟨idxN, j⟩) := by
    simpa [homeT, homes] using hs
  rcases homesFrom_mem _ _ _ s hs' with h | h
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    exact ⟨hT.there, ho j hj⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    exact ⟨hi, hk j hj⟩

end Johnson.RunOne.Law.FitsKeyD

#print axioms Johnson.RunOne.Law.FitsKeyD.homesFrom_mem
#print axioms Johnson.RunOne.Law.FitsKeyD.fits_of_lists
