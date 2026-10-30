-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Live/Bare.lean: the proofs of `HeadMergeBareBehind`, `MergeBareHands` and
`MergeRunBare` (Johnson/Desc/K11/Live/BareStatement.lean), to the letter. Lemmas; none of the
library's goals.

How: the library's lemmas. The first: `decide_inv` (Johnson/Top/H0/MergeLaw/Says.lean) and
`hear_ended` (Said.lean of that folder): the sumcheck's start is `wsForkStart` of the claim's slot.
The second: by the definition. The third: `claim_inv` (Run.lean of that folder): the run returns one
claim, of the form `Psc.rowForm`, with no run of entries, and turns the ledger alone; `rowForm_ents`
(MergeMakesForms.lean of that folder): at such a start that form names no entry.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Live.BareStatement
import Johnson.Top.H0.MergeLaw.MergeMakesForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Live
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.First.MergeLaw (decide_inv hear_ended claim_inv rowForm_ents)

/-- **Behind the decision's yes the start is the merge's own.** -/
theorem headMergeBareBehind : HeadMergeBareBehind := by
  intro P s s' rs h
  obtain ⟨a, a', tp, F, claim, x, wo, _, ha', _, _, hwo, _, hm, _, _, _, _⟩ := decide_inv h
  obtain ⟨xs, mu, c, beta, v, T, r1, rY, rV, qs, _, _, _, _, hE, _, _, _, _, _, _⟩ := hear_ended hm
  exact ⟨a', wo, _, _, ha', hwo, hE.start⟩

/-- **A step that leaves the field hands the condition on.** -/
theorem mergeBareHands : MergeBareHands := by
  intro u u' a a' ha ha' hw hB
  obtain ⟨a0, wo, sv, rho, ha0, hwo, hs⟩ := hB
  obtain rfl : a0 = a := Here.head.inj (ha0.symm.trans ha)
  exact ⟨a', wo, sv, rho, ha', hw.trans hwo, hs⟩

/-- **The run's claim names no entry and no run of entries; the condition is handed on.** -/
theorem mergeRunBare : MergeRunBare := by
  intro n s z hB h
  obtain ⟨cls, s'⟩ := z
  obtain ⟨a, wo, G, ha, hwo, rfl, rfl, _⟩ := claim_inv h
  obtain ⟨a0, wo0, sv, rho, ha0, hwo0, hs⟩ := hB
  obtain rfl : a0 = a := Here.head.inj (ha0.symm.trans ha)
  obtain rfl : wo0 = wo := Option.some.inj (hwo0.symm.trans hwo)
  refine ⟨fun cl hcl => ?_, _, wo0, sv, rho, rfl, hwo, hs⟩
  obtain rfl : cl = { form := wo0.p.rowForm wo0.fvp {} } := List.mem_singleton.1 hcl
  exact ⟨Array.ext' (rowForm_ents _ _ sv rho hs), rfl⟩

end Johnson.Desc.First.ForkMerge.Live

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Live.headMergeBareBehind
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeBareHands
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeRunBare
