-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimOfQuiet.lean: the proofs of `HeadClaimOfRun` and
`HeadClaimOfQuiet` (Honest/K11/ClaimOfQuietStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The core first; the quiet step's by it. Which claim the quiet step lays: `K3.quietHead_claim`
(Johnson/Desc/First/Look/K3QuietLaws.lean). The covered positions: `coveredAt`
(Johnson/Desc/First/State.lean) reads of the state the request's words alone, and of the token one
test; where it returns, which positions are covered is said by the words (`coveredAt_on`). Of its
run `weightsClaim` reads of what the head heard four fields, and of the covered positions that one
(`weightsClaim_reads`, `weightsClaim_reads_on`, Honest/K11/Claims.lean). NEAR. `coveredAt_same`
(Johnson/AtFull/Shape/ReqAtHead.lean): at one token, two states with the same words: one return;
`coveredAt_on` lets the token turn too, and so ends at the covered positions alone.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimOfQuietStatement
import Johnson.Desc.First.Look.K3QuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (weightsClaim)
open VerifiableInference.Desc.K3 (quietHead quietHead_claim)

/-- Where `coveredAt` returns at a state and a token, it returns at every state with the same words
and every entry of the vocabulary, with the same positions covered. -/
theorem coveredAt_on (T V y y₂ : Nat) (s s₂ : S) (cov : Head.Covered) (hreq : s₂.req = s.req)
    (hy : y₂ < V) (h : s.coveredAt T V y = .ok cov) :
    ∃ cov₂, s₂.coveredAt T V y₂ = .ok cov₂ ∧ cov₂.hOn = cov.hOn := by
  unfold S.coveredAt at h ⊢
  rw [hreq]
  dsimp only at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2 h3 h4
          obtain rfl := Except.ok.inj h
          rw [if_neg (by simp [hy]), if_neg h2, if_neg h3, if_neg h4]
          exact ⟨_, rfl, rfl⟩

/-- **The core: the claim at the run made of the state is the text's.** -/
theorem headClaimOfRun : HeadClaimOfRun := by
  intro H Z G x heard s cov hx t' claim hcov hw hreq hy k1 k2 k3 k4
  have hcov' : ∃ y, s.coveredAt G.W.T G.W.P.h.V y = .ok cov := by
    unfold S.covered at hcov
    cases hr : s.replyTok? with
    | none =>
      rw [hr] at hcov
      cases hcov
    | some y =>
      rw [hr] at hcov
      exact ⟨y, hcov⟩
  obtain ⟨y, hcy⟩ := hcov'
  obtain ⟨cov₂, hc₂, hon⟩ :=
    coveredAt_on G.W.T G.W.P.h.V y _ s (startS Z x.pub) cov hreq.symm hy hcy
  have e1 : headHeardAt (H Z G) x heard = heardOfFour hx.g1.zk hx.tH.r hx.rs hx.win := by
    unfold headHeardAt
    rw [k1, k2, k3, k4]
  have key : weightsClaim
      { h := G.W.hS, L := G.W.HLy, b := Verify.borderOf G.W.y, hp := G.W.H, cov := cov₂
        x := headHeardAt (H Z G) x heard, t := {}
        iU3 := (G.W.H.tl.ix.U.getD 2 none).getD 0 } G.W.layers.wsLay = .ok claim := by
    rw [e1, ← hw]
    cases cov₂ with
    | mk tk on wn oc rc =>
      have hon' : on = cov.hOn := hon
      subst hon'
      exact (weightsClaim_reads_on
        { h := G.W.hS, L := G.W.HLy, b := Verify.borderOf G.W.y, hp := G.W.H, cov := cov
          x := heardOfFour hx.g1.zk hx.tH.r hx.rs hx.win, t := {}
          iU3 := (G.W.H.tl.ix.U.getD 2 none).getD 0 } G.W.layers.wsLay ⟨tk, #[], wn, oc, rc⟩).trans
        (weightsClaim_reads
          { h := G.W.hS, L := G.W.HLy, b := Verify.borderOf G.W.y, hp := G.W.H, cov := cov
            x := hx, t := t', iU3 := (G.W.H.tl.ix.U.getD 2 none).getD 0 } G.W.layers.wsLay {}
          ((G.W.H.tl.ix.U.getD 2 none).getD 0) (Verify.borderOf G.W.y))
  unfold headMergeClaims headRunAt
  rw [hc₂]
  show (match weightsClaim _ G.W.layers.wsLay with
    | .ok q => [q]
    | .error _ => []) = [claim]
  rw [key]

/-- **The claim that the quiet step lays is the text's.** -/
theorem headClaimOfQuiet : HeadClaimOfQuiet := by
  intro H Z G x heard s t h hreq hy hties
  obtain ⟨a, cov, hx, t', claim, ha, hcov, hax, _, hw, _, rfl⟩ := quietHead_claim G.W s t h
  obtain ⟨k1, k2, k3, k4⟩ := hties a hx ha hax
  exact ⟨_, claim, rfl, rfl,
    headClaimOfRun H Z G x heard s cov hx t' claim hcov hw hreq hy k1 k2 k3 k4⟩

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.coveredAt_on
#print axioms ProofFile.Honest.K11.headClaimOfRun
#print axioms ProofFile.Honest.K11.headClaimOfQuiet
