-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK1.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach: THE FIELD k1 OF
KeepShares (RoomKeep.lean), IN THAT STRUCTURE'S OWN LETTERS: every sub-protocol of the kind K1
(a sending) that a lot of the seat makes inside a link, but at the link's first place, hands both
clauses on.

  k1_keeps          THE FIELD: one term over k1_hands (Johnson/Desc/AtSeats/RoomK1.lean),
                    which has the field's content in plain letters. The term is that file's head's
                    own, typed there as a comment; here it is through Lean.

Limits. One field of thirteen. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.Desc.AtSeats.RoomK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **THE FIELD k1 OF KeepShares.** -/
theorem k1_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) → b'.place.chain = 1 →
      b'.place.kind = KindName.K1 → b'.place.link ≠ none → b'.place.piece ≠ 1 →
      KeepsAt c start (numberOf b'.place) b' :=
  fun b' hm _ hk hl hp _ _ _ _ hy hout _ hn =>
    (VerifiableInference.Desc.K1.k1_hands b' hm hk hl hp hy hn (outOfGroupsB_iff.1 hout)).imp id
      outOfGroupsB_iff.2

end P1L20

#print axioms P1L20.k1_keeps
