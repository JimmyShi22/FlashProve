-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/LotLinks.lean: a segment at which the lot reads the batching's numbers is in the lot's
own list of segments. One lemma on two texts of the library (`k9Where`, `k9Links`, Johnson/Desc/ProofFile/Lot/K9.lean);
for the kinds K9 and K10 alike; it imports that file alone.

  `links_of_where`   `k9Where xs l = some p` gives `l ∈ k9Links xs`

Limits. Nothing here on how often l is listed (once, under `IM.Open`: `links_once`,
Johnson/Desc/K10/Honest/LinksOnce.lean, where this lemma stands too, as `where_in_links`). No property of the protocol
is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Lot.K9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

/-- Where `k9Where` yields numbers at l, `k9Links` lists l. -/
theorem links_of_where {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)} {l : Nat}
    {p : VerifiableInference.Desc.K9.Where}
    (h : ProofFile.k9Where xs l = some p) : l ∈ ProofFile.k9Links xs := by
  unfold ProofFile.k9Where at h
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hx
  have hp := List.find?_some hx
  unfold ProofFile.k9Links
  refine List.mem_filterMap.2 ⟨x, hm, ?_⟩
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨h1, h2⟩)]
  exact eq_of_beq h3

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.links_of_where
