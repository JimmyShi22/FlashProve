-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5AttOf.lean: kind K5: AT A STATE WITH AN OPEN ATTENTION SEGMENT, what two theorems along the fold conclude (in the state's own readers lookHeard? | fork?) gives the yes of the wider filling's two tests bareAttB | leftAttB (Att/Door/Plus.lean). A LIGHT FILE: it imports
the tests' own file and Att/K05BehindLay.lean alone, so that whoever has "an attention segment is open" in hand can call the two without the bridge.
  bareAtt_of · leftAtt_of: cut, to the letter, out of Door/Law/K5ReachedPlus.lean, which imports this file for them.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Plus
import Johnson.Desc.First.Att.K05BehindLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (fork_front lookHeard_front)

theorem bareAtt_of {s : S} {att : AttOwn} (e : s.here = .att att)
    (h : ∃ g, s.lookHeard? = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[]) : bareAttB s = true := by
  obtain ⟨g, hg, hb⟩ := h
  rw [lookHeard_front e] at hg
  unfold bareAttB
  rw [e]
  simp only [hg, Option.any_some, List.all_eq_true]
  intro f hf
  rw [hb f hf]
  rfl

theorem leftAtt_of {s : S} {att : AttOwn} (e : s.here = .att att)
    (h : ∃ g G, s.lookHeard? = some g ∧ s.fork? = some G ∧ FillBare.leftAtB g G = true) : leftAttB s = true := by
  obtain ⟨g, G, hg, hG, hl⟩ := h
  rw [lookHeard_front e] at hg
  obtain rfl : att.F = G := Option.some.inj ((fork_front e).symm.trans hG)
  unfold leftAttB
  rw [e]
  simp only [hg, Option.any_some]
  exact hl

end H2K5.Door

#print axioms H2K5.Door.bareAtt_of
#print axioms H2K5.Door.leftAtt_of
