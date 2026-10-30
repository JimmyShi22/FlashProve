-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK6K7.lean: ON THE PATTERN OF
P1L20R/RoomKeepK8.lean: TWO SHARES OF THE KEEPING BENEATH room_at_reach, PAID: THE FIELDS k6 AND k7
OF KeepShares (P1L20R/RoomKeep.lean).

  k6_keeps          THE FIELD k6: every sub-protocol of the kind K6 (the output head's own rounds)
                    that a lot of the seat makes leaves the chain's statement and all that was put
                    out as they were: hands2_same.
  k7_keeps          THE FIELD k7: the sub-protocol of the kind K7 that a lot of the seat makes is
                    the quiet entry into the head's link, then the next token's: IT LAYS ONE FRESH
                    GROUP: so not by hands2_same: the oracle messages and the number of the index
                    masks' message are as they were, so that message's ledger is; every group behind
                    is a group in front or has no member, so the message is a member of none.
  Both at every Z, G, c and start: no scope is asked; neither "chain 1" nor "reached" is spent.

BY Johnson/Desc/Kinds/Law/K6K7LotLeaves.lean (k6Hear_leaves · h1Own_keeps) and
IMR/LotKinds.lean (lot_of_kind · blocks_mem) and IMR/K7Seat.lean (lot_K7).
Limits. Two fields of thirteen. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.IMR.K7Seat
import Johnson.Desc.Kinds.Law.K6K7LotLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (k6Hear_leaves h1Own_keeps)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- **THE FIELD k6 OF KeepShares.** -/
theorem k6_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K6 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = P4.k6Lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  have hm : b' ∈ P4.k6Hear Z G₀ := by
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · cases hx
    · exact h
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  obtain ⟨e1, e2⟩ := k6Hear_leaves hm e
  exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout

/-- **THE FIELD k7 OF KeepShares.** -/
theorem k7_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K7 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout n hn
  obtain ⟨x, hx, rfl⟩ := IM.lot_K7 hL hb hk
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  obtain ⟨e1, e2, e3⟩ := h1Own_keeps hx (show x.decide s rs gs = .ok s' from e)
  have hl : Johnson.Desc.First.Walk.Law.ledgerAt s' = Johnson.Desc.First.Walk.Law.ledgerAt s := by
    unfold Johnson.Desc.First.Walk.Law.ledgerAt
    rw [e1, e2]
  refine ⟨by rw [leftIsB_of_ledger hl]; exact hn, ?_⟩
  rw [outOfGroupsB_iff] at hout ⊢
  intro Gr hG
  rcases e3 Gr hG with h | h
  · rw [e2]
    exact hout Gr h
  · rw [h]
    simp

end P1L20

#print axioms P1L20.k6_keeps
#print axioms P1L20.k7_keeps
