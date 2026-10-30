-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK8.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach, PAID: THE FIELD k8 OF
KeepShares (RoomKeep.lean): every sub-protocol of the kind K8 (the approximate range proof's
first half) that a lot of the seat makes leaves the chain's statement and all that was put out as
they were: so the index-mask message's ledger, the groups and that message's number.

  k8_same           an accepting decision of the kind, whole, leaves the statement and what was put
                    out: hear_leaves_statement, hear_leaves_out
                    (Johnson/Desc/First/K8/LawLeaves.lean)
  k8_keeps          THE FIELD, at every Z, G, c and start: no scope is asked; neither "chain 1" nor
                    "reached" is spent

Limits. One field of thirteen. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.IMR.K8Seat
import Johnson.Desc.First.K8.LawLeaves
import Johnson.Desc.First.K8.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- An accepting decision of the kind, whole, leaves the statement and all that was put out. -/
theorem k8_same (p : VerifiableInference.Desc.First.K8.ParW) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.First.K8.whole p).decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out :=
  ⟨VerifiableInference.Desc.First.K8.hear_leaves_statement (Cl := Cl) p.toPar s rs gs s' h,
    VerifiableInference.Desc.First.K8.hear_leaves_out (Cl := Cl) p.toPar s rs gs s' h⟩

/-- **THE FIELD k8 OF KeepShares.** -/
theorem k8_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K8 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = ProofFile.P1K8.lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  have hm : b' ∈ (ProofFile.P1K8.lot Z).hearC G₀ := by
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · cases hx
    · exact h
  obtain ⟨l, Xl, -, rfl⟩ := IM.k8Whole_mem hm
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  obtain ⟨e1, e2⟩ := k8_same _ e
  exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout

end P1L20

#print axioms P1L20.k8_same
#print axioms P1L20.k8_keeps
