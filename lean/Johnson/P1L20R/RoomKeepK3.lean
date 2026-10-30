-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK3.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach: THE FIELD k3 OF
KeepShares (RoomKeep.lean): every sub-protocol of the kind K3 (a lookup argument's hearing)
that its lot makes leaves the chain's statement and all that was put out as they were.

  k3_keeps          THE FIELD, at every Z, G, c and start: no scope is asked; neither "chain 1" nor
                    "reached" is spent. By k3_lot_same
                    (Johnson/Desc/First/Look/K3LotLeaves.lean).

WHENCE. The theorem's statement and its nine lines of proof are written
after P1L20R/RoomKeepK8.lean's k8_keeps.



Limits. One field of thirteen. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.IMR.LotKinds
import Johnson.Desc.First.Look.K3LotLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- **THE FIELD k3 OF KeepShares.** -/
theorem k3_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K3 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = K3Lot.lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  have hm : b' ∈ K3Lot.hear Z := by
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · cases hx
    · exact h
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  obtain ⟨e1, e2⟩ := VerifiableInference.OnPublicFiles.k3_lot_same Z hm e
  exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout

end P1L20

#print axioms P1L20.k3_keeps
