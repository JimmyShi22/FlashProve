-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RoomKeepK4.lean: K4's SHARE OF THE KEEPING BENEATH "the index masks' ledger has just
so many entries left at every reached state": THE FIELD k4 OF THE STRUCTURE `P1L20.KeepShares`
(Johnson/P1L20R/RoomKeep.lean), to the letter. Two statements with their proofs; the second follows
that file's authors' own proof for K8's field line by line.

  `k4_same`: an accepting decision of a sub-protocol of K4's lot leaves the statement and all that
    was put out. (The lot's sub-protocol is K4's own term with another test on the plan: its
    decision is that term's; `k4C_whole_rest`, K4WholeSt.lean.)
  **`k4_keeps`**: `LotKeeps Z G₀ c start KindName.K4`, at every Z, G₀, c, start: NO PREMISE: neither
  the goals' scope nor "reached" nor "chain 1" is spent.

Limits. One of thirteen shares: it says what K4's twelve sub-protocols LEAVE, not that the ledger
has any entries left. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.
-/
import Johnson.P1L20R.RoomKeep
import Johnson.Road.K4.K4WholeSt
import Johnson.Desc.ProofFile.Lot.K4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open P1L20 (LotKeeps hands2_same)
open ProofFile (Cl)

/-- An accepting decision of a sub-protocol of K4's lot leaves the statement and all that was put
out. -/
theorem k4_same (x : Bool × OnBytes.Desc.First.K4.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (ProofFile.k4Block x).decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out :=
  have R := (k4C_whole_rest { x.2 with k3Runs := true }).1 s rs gs s' h
  ⟨R.st, R.out⟩

/-- **THE FIELD k4 OF KeepShares.** -/
theorem k4_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K4 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = ProofFile.k4Lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  have hm : b' ∈ (ProofFile.k4Lot Z).hearC G₀ := by
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · cases hx
    · exact h
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  obtain ⟨e1, e2⟩ := k4_same x e
  exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_same
#print axioms OnBytes.Road.K4.k4_keeps
