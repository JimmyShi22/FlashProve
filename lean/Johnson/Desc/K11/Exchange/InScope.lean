-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/InScope.lean: the proof of `HeadMergeInScope`
(Johnson/Desc/K11/Exchange/InScopeStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. All by the library's own lemmas: the head's link's hearing block number 8 is the lot's block,
alone, at the kind's address (`IM.k11_of`, Johnson/IMR/K11Seat.lean); a link's hearing block stands
in the flat list at a number that is a term of the chain (`IM.hear_at_flat`,
Johnson/IMR/FlatIx.lean), which in scope is 14 l + i + 2 (`IM.flatIx_scope`,
Johnson/IMR/FlatScope.lean). The reader of a link off the public part alone reads the opened chain
(`P5J.chain_free`, Johnson/P5J/ChainFree.lean). The lot's block is the kind's at the lot's numbers:
`lotBlockIs` (AtSeat.lean of this folder).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.InScopeStatement
import Johnson.Desc.K11.Exchange.AtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)

/-- **The kind's block in the description's first chain, in scope.** -/
theorem headMergeInScope : HeadMergeInScope := by
  intro P pp lay F Z Bs base c A B hS hR O hfound
  obtain ⟨Lk, b, e1, e2, hla, hlink⟩ := IM.k11_of hS hR O
  have hb : b = IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Z Bs.G₀)) b.name IM.k11Place := by
    have h0 : b = IM.seatedAs ProofFile.sameReply (K11.blkAt Z "H.8.call" Bs.G₀) b.name IM.k11Place := hla
    rw [lotBlockIs Z "H.8.call" Bs.G₀ hfound] at h0
    exact h0
  have hfl : c.blocksInOrder[346]? = some b := by
    have q := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (Nat.le_refl 24) 8] at q
  have hl : ProofFile.linkAt Z 24 = some Lk := by
    unfold ProofFile.linkAt
    rw [P5J.chain_free O]
    exact e1
  refine ⟨Lk, b.name, e1, hl, ?_, ?_, hlink⟩
  · rw [← hb]
    exact e2
  · rw [← hb]
    exact hfl

end Johnson.Desc.First.ForkMerge.Exchange

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.headMergeInScope
