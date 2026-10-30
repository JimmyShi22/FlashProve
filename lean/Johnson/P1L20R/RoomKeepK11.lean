-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK11.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach, PAID: THE FIELD k11 OF
KeepShares (RoomKeep.lean): the sub-protocol of the kind K11 (the merge of the claims on the
weight table, at the head's link's end) that its lot makes leaves the chain's statement and all that
was put out as they were: so the index-mask message's ledger, the groups and that message's number.

  k11_same          an accepting decision of the kind writes two fields of the verifier's state
                    alone (what is owed; the head's own part): by isLocal
                    (Johnson/Top/H0/MergeLaw/Law.lean)
  k11_keeps         THE FIELD, at every Z, G, c and start: no scope is asked; neither "chain 1" nor
                    "reached" is spent. The lot's one member: lot_lays, blkAt_decide
                    (Johnson/Top/H0/MergeLaw/LotIs.lean)

Limits. One field of thirteen. The kind READS the ledger's next entry; it takes none. No soundness
statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Top.H0.MergeLaw.LotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open ProofFile (Cl)

/-- An accepting decision of the kind leaves the statement and all that was put out. -/
theorem k11_same (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') : s'.st = s.st ∧ s'.out = s.out := by
  obtain ⟨a, a', _, _, e3, _⟩ := VerifiableInference.Desc.First.MergeLaw.isLocal P s rs s' h
  rw [e3]
  exact ⟨rfl, rfl⟩

/-- **THE FIELD k11 OF KeepShares.** -/
theorem k11_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K11 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = K11.lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  have hm : b' ∈ (K11.lot Z).hearC G₀ := by
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · cases hx
    · exact h
  rw [(K11.lot_lays Z G₀).1] at hm
  obtain rfl := List.mem_singleton.1 hm
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  rw [K11.blkAt_decide] at e
  obtain ⟨e1, e2⟩ := k11_same _ e
  exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout

end P1L20

#print axioms P1L20.k11_same
#print axioms P1L20.k11_keeps
