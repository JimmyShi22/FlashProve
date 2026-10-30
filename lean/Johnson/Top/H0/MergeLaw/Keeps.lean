-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Keeps.lean: the merge keeps the ledger: wherever `mergeHear`, the block's
decision
or its run of claims says yes, the ledger behind is later than the one in front
(`OnBytes.PscRun.Later`, OnBytes/Tie/Pv/Psc/PscLater.lean): as many slots; no fewer taken; every
slot
that was filled is filled and holds the same shown value and the same factor. Three theorems with
their proofs: `hear_later`, `decide_later`, `run_later`. No premise on the arrays' sizes.

The library's `Later`, Later.trans and hideRun_keeps (PscLater.lean) are spent: statements on plain
records.

Limits: a block that never says yes has all this emptily. Nothing on which values are laid, on
soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Says
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E)
open OnBytes.K.Kc (Tape)
open OnBytes.Model (Fork WsLay WsClaim WsForkOut)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Claim)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim mergeHear)

/-- Where `mergeHear` says yes, the ledger that it leaves is later than the one that it was handed.
No premise on the arrays' sizes. -/
theorem hear_later {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' : Tape}
    {wo : WsForkOut}
    (h : mergeHear lay cl sv F t = .ok (wo, F', t')) : Later F F' := by
  obtain ⟨_, _, _, beta, v, _, _, _, _, _, _, _, _, _, _, _, _, _, hhide, _⟩ := hear_ended h
  have h1 : Later F { F with next := F.next + 1 + 2 * lay.lk + 2 } :=
    ⟨by show F.next ≤ F.next + 1 + 2 * lay.lk + 2; omega, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩
  exact h1.trans (OnBytes.PscRun.hideRun_keeps hhide)

/-- **The merge's block keeps the ledger**: where the decision says yes, the head's ledger behind is
later than the one in front. -/
theorem decide_later {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide P s rs =
           .ok s') :
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ Later a.F a'.F := by
  obtain ⟨a, a', _, G, _, _, _, ha, ha', _, _, _, _, hm, hF, _⟩ := decide_inv h
  refine ⟨a, a', ha, ha', ?_⟩
  rw [hF]
  exact (hear_later hm).trans ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- So does its run of claims. -/
theorem run_later {n : Nat} {s s' : S} {cls : List Claim} (h : headMergeClaim n s = .ok (cls, s')) :
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ Later a.F a'.F := by
  obtain ⟨a, _, G, h1, _, h2, _, h4⟩ := claim_inv h
  exact ⟨a, { a with F := G }, h1, by rw [h2], OnBytes.PscRun.hideRun_keeps h4⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.decide_later
#print axioms VerifiableInference.Desc.First.MergeLaw.run_later
