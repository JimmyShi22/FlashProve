-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Run.lean: the merge's one run of claims (`headMergeClaim`,
Johnson/Desc/First/Fork/MergeKind.lean). Theorems with their proofs.

Main names:
  `claim_inv`: where the run says yes: one claim; its form is the form that the sumcheck leaves
    (Psc.rowForm) at the shown end value; of the record the head's ledger alone turns.
  `run_leaves_wo`: the run leaves what the merge has left in the record.
  `claims_leave`, `after_leave`: the block's runs leave the reply that was heard.

Limits: that other blocks' runs leave what the merge has left is not said. Nothing on soundness or
on
hiding.

-/
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Top.H0.MergeLaw.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E zeroE oneE subE)
open OnBytes.K.Kc
open VerifiableInference.Desc (Claim)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headClaimMergeKind)

/-- **What the run's yes holds**: the record stands in the head's link; there is one claim, and its
form is the form that the
sumcheck leaves (`Psc.rowForm`) at the shown end value; of the record the head's ledger alone turns:
it gets the pairs (0, -1)
under the slots of the hiding polynomial's coefficients. -/
theorem claim_inv {n : Nat} {s s' : S} {cls : List Claim} (h : headMergeClaim n s = .ok (cls, s')) :
    ∃ a wo G, s.here = .head a ∧ a.wo = some wo ∧ s' = { s with here := .head { a with F := G } } ∧
      cls = [{ form := wo.p.rowForm wo.fvp {} }] ∧
      a.F.hideRun wo.p.first (Array.replicate wo.p.walk.1.length zeroE) (subE zeroE oneE) = some G
          := by
  unfold headMergeClaim at h
  cases hh : s.here with
  | head a =>
    simp only [hh] at h
    obtain ⟨wo, a0, h⟩ := ebind_inv h
    obtain ⟨⟨⟨form, p'⟩, F', t'⟩, a1, k1⟩ := ebind_inv h
    obtain ⟨e1, _, _, e4, _⟩ := pscRow_inv (named_ok a1)
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at k1
    obtain ⟨k1, k2⟩ := k1
    exact ⟨a, wo, F', rfl, named_ok a0, k2.symm, by rw [← k1, e1], e4⟩
  | _ => simp [hh] at h

/-- The run leaves what the merge has left in the record, and all else of the head's part but the
ledger. -/
theorem run_leaves_wo {n : Nat} {s s' : S} {cls : List Claim} (h : headMergeClaim n s = .ok (cls,
    s')) :
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ a'.wo = a.wo ∧ a'.claim = a.claim ∧ a'.x = a.x ∧
        a'.Fm = a.Fm ∧
      a'.slot = a.slot := by
  obtain ⟨a, _, G, h1, _, h2, _, _⟩ := claim_inv h
  exact ⟨a, { a with F := G }, h1, by rw [h2], rfl, rfl, rfl, rfl, rfl⟩

/-- Every run of claims of the block leaves the reply that was heard. -/
theorem claims_leave (P : HeadMergeP) : ∀ c ∈ (headClaimMergeKind P).claims, ∀ (n : Nat) (s : S) (cls :
           List Claim) (s' : S),
    c.2 n s = .ok (cls, s') → s'.out.reply = s.out.reply := by
  intro c hc n s cls s' h
  have hc' : c = ("the merge", headMergeClaim) := by simpa [headClaimMergeKind] using hc
  subst hc'
  obtain ⟨a, _, G, _, _, h2, _, _⟩ := claim_inv (n := n) h
  rw [h2]

/-- The block has no run behind the batching. -/
theorem after_leave (P : HeadMergeP) : ∀ c ∈ (headClaimMergeKind P).after, ∀ (s s' : S),
    c.2 s = .ok s' → s'.out.reply = s.out.reply := by
  intro c hc
  simp [headClaimMergeKind] at hc

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.claim_inv
#print axioms VerifiableInference.Desc.First.MergeLaw.claims_leave
