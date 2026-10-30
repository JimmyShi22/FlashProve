-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsSeat.lean: the proof of `HeadMergeKeepsSeat`
(Johnson/Desc/K11/Returns/KeepsSeatStatement.lean), to the letter. A lemma; none of the library's
goals.

How. The clause writes the state behind out of the state in front: the link is opened in front, and
of the head's own part the member turns four fields, neither "opened" nor the tail among them. The
ledgers: `headMergeKeepsLater` (KeepsLater.lean of this folder).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsSeatStatement
import Johnson.Desc.K11.Returns.KeepsLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open VerifiableInference.Desc.First (S Here)

/-- **What the two shared readings answer past the merge's member.** -/
theorem headMergeKeepsSeat : HeadMergeKeepsSeat := by
  intro P s s' hk
  obtain ⟨a, a', ha, ha', hL, hL'⟩ := headMergeKeepsLater P s s' hk
  obtain ⟨⟨b, wo, v, β, hb, ho, _, _, _, _, e⟩, _⟩ := hk
  obtain rfl : b = a := Here.head.inj (hb.symm.trans ha)
  rw [e] at ha'
  obtain rfl := Here.head.inj ha'
  have hF : s.fork? = some b.F := by
    simp [S.fork?, ha, ho]
  refine ⟨?_, ⟨b.F, hF⟩, ?_⟩
  · rw [e]
    simp [S.tl?, ha, ho]
  · intro F hF'
    obtain rfl : b.F = F := Option.some.inj (hF.symm.trans hF')
    refine ⟨_, ?_, hL, hL'⟩
    rw [e]
    simp [S.fork?, ho]

end Johnson.Desc.First.ForkMerge.Returns

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeKeepsSeat
