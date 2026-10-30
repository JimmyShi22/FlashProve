-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K3Stays.lean: WHAT THE LOOKUP ON THE DIGITS LEAVES OF THE OPEN
SEGMENT's OWN PART. The kind K3 has its clause of the letter `keeps`
at a lookup on the digits of a layers' or an attention segment (`K3KeepsDigits`): the state
behind is the state in front with tl and F of the open part turned. So g of an attention segment's
part and own of a layers' segment's part are as they were. Cut out of Honest/Thread/AttGStays.lean
and LayOwnStays.lean, names and statements unturned, because that clause's file stands over many
files of its house, of which these two lemmas spend one definition. No definition. Two conditional
lemmas.

  `attG_k3`, `layOwn_k3`

Limits. `K3KeepsDigits` IS NOT THE CLAUSE THAT THE HOUSE HANDS IN FOR `keeps`: that one goes by the
place: `k3KeepsAt Z p` (Honest/K3/Law/Thread/K3KeepsAt.lean): it gives `K3KeepsDigits` only where a
site of `lookSites Z` stands at p, is on the digits, and the step without a round behind it has the
form `quietDigits` (`k3KeepsAt_digits`): three public facts, shown here at no place; WHERE NO SITE
STANDS AT p IT HOLDS OF EVERY PAIR OF STATES (`k3KeepsAt_else`), and these two lemmas' premise is
then not to be had. It stands over files of other houses which are not sealed: how many, and whose,
its cover says by a count on the machine that compiled it. None is one of the library's goals.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

/-- The lookup on the digits of a layers' or an attention segment. -/
theorem attG_k3 {sh : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : S}
    (h : ProofFile.Honest.K3.Law.AtThr.K3KeepsDigits sh claims s s') :
    ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨-, tl, F, H, G, -, -, hA, -⟩ := h
  intro a ha
  rcases hA with ⟨a₁, h1, -⟩ | ⟨a₁, h1, rfl⟩ | ⟨a₁, h1, -, -⟩
  · rw [ha] at h1
    cases h1
  · rw [ha] at h1
    cases h1
    exact ⟨_, rfl, rfl⟩
  · rw [ha] at h1
    cases h1

/-- The lookup on the digits of a layers' or an attention segment. -/
theorem layOwn_k3 {sh : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : S}
    (h : ProofFile.Honest.K3.Law.AtThr.K3KeepsDigits sh claims s s') :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  obtain ⟨-, tl, F, H, G, -, -, hA, -⟩ := h
  intro a ha
  rcases hA with ⟨a₁, h1, rfl⟩ | ⟨a₁, h1, -⟩ | ⟨a₁, h1, -, -⟩
  · rw [ha] at h1
    cases h1
    exact ⟨_, rfl, rfl⟩
  · rw [ha] at h1
    cases h1
  · rw [ha] at h1
    cases h1

end ProofFile.Honest

#print axioms ProofFile.Honest.attG_k3
#print axioms ProofFile.Honest.layOwn_k3
