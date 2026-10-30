-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/KeepsHead.lean: THE SMALLNESS TEST: WHAT THE KIND's CLAUSE OF THE LETTER
keeps (`K8KeepsM`, Johnson/Desc/K8/Honest/KeepsMark.lean) LEAVES OF THE OUTPUT HEAD's OWN PART OF
THE STATE, IN THE FORM IN WHICH A SENTENCE ON THAT PART IS CARRIED PAST A MEMBER THAT TURNS A FIELD
OF IT. Lemmas on the verifier's own text; none of the library's goals.

  **`K8Keeps.head`**, `K8KeepsM.head`   ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x =
                   a.x ∧ a'.t = a.t ∧ a'.wo = a.wo: what the head's own rounds heard, its tables,
                   and what the merge has left are as they were
  `K8Keeps.head_of`   so every sentence P on the head's own part that does not read the test's data
                   stays: (∀ a tl', P a → P { a with tl := tl' }) → P a → P a'
By `keeps_head`: the part behind is the part in front but for the test's data.
Limits. From the clause alone. The head's segment alone; the like for the two other sorts:
`keeps_lay`, `keeps_att`.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.KeepsMark

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model VerifiableInference.Desc.First

/-- **Three fields of the head's own part are as they were.** -/
theorem K8Keeps.head {s s' : S} (h : K8Keeps s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  intro a ha
  obtain ⟨tl', e⟩ := keeps_head h ha
  exact ⟨_, e, rfl, rfl, rfl⟩

theorem K8KeepsM.head {s s' : S} (h : K8KeepsM s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo :=
  h.1.head

/-- Every sentence on the head's own part that does not read the test's data stays. -/
theorem K8Keeps.head_of {s s' : S} (h : K8Keeps s s') (P : HeadOwn → Prop)
    (hP : ∀ a tl', P a → P { a with tl := tl' }) :
    ∀ a, s.here = .head a → P a → ∃ a', s'.here = .head a' ∧ P a' := by
  intro a ha hp
  obtain ⟨tl', e⟩ := keeps_head h ha
  exact ⟨_, e, hP a tl' hp⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.head
#print axioms VerifiableInference.Desc.First.K8.Honest.K8KeepsM.head
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.head_of
