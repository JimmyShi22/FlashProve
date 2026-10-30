-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK5.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach: THE FIELD k5 OF
KeepShares (RoomKeep.lean): every sub-protocol of the kind K5 (the hearing of an attention
segment's own rounds) that a lot of the seat makes leaves the chain's statement and all that was put
out as they were: so the index-mask message's ledger, the groups and that message's number.
TYPED AFTER k8_keeps (Johnson/P1L20R/RoomKeepK8.lean): its first two and its last three lines, two names turned; its five lines on K8's own
sub-protocol have no like here, since lotN_decide_stOut speaks of every sub-protocol of the lot.

  k5_keeps          THE FIELD, at every Z, G, c and start: no scope is asked; neither "chain 1" nor
                    "reached" is spent. By lotN_decide_stOut
                    (Johnson/Desc/First/Att/K05LeavesOut.lean: one of K5's files; over
                    Johnson/Desc/First/Att/K05Leaves.lean)

Limits. One field of thirteen. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.IMR.LotKinds
import Johnson.Desc.First.Att.K05LeavesOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- **THE FIELD k5 OF KeepShares.** -/
theorem k5_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K5 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = H2K5.lotN Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  obtain ⟨e1, e2⟩ := VerifiableInference.Desc.First.Att.P.lotN_decide_stOut hb e
  exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout

end P1L20

#print axioms P1L20.k5_keeps
