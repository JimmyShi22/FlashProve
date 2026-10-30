-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/Seat.lean: the proofs of `HeadMergeRecs`, `HeadMergeLeavesReply` and
`HeadMergeSeated` (Johnson/Desc/K11/Returns/SeatStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. All by the library's own lemmas that take a return apart: the decision's: `decide_inv`
(Johnson/Top/H0/MergeLaw/Says.lean); the hearing's: `mergeHear_inv`
(Johnson/Top/H0/MergeLaw/Hear.lean); the run's: `claim_inv` (Johnson/Top/H0/MergeLaw/Run.lean); that
the decision leaves seven fields of the state: `leavesSeven` (Johnson/Top/H0/MergeLaw/Law.lean);
that a block which never writes the seat is its guarded form: `Block.Still.guarded_eq`
(Johnson/Desc/Sound/SeatGuardChain.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.SeatStatement
import Johnson.Top.H0.MergeLaw.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E oneE mulE)
open OnBytes.Model (WsClaim WsForkOut wsRowPart wsEpsT powers)
open VerifiableInference.Desc (Place Claim Block)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (decide_inv mergeHear_inv claim_inv leavesSeven)

/-- **The parts for the row, in the form in which the hearing lays them.** -/
theorem headMergeRecs : HeadMergeRecs := by
  intro P s s' rs h
  obtain ⟨a, a', tp, F, claim, x, wo, h1, h2, h3, _, h5, _, h7, _⟩ := decide_inv h
  obtain ⟨xb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrecs, _⟩ :=
    mergeHear_inv h7
  refine ⟨a, a', claim, wo, h1, h2, h3, h5, ?_⟩
  rw [hrecs]
  show ((#[claim].zip (powers xb 1)).toList.map _) = _
  have hp : powers xb 1 = #[oneE] := rfl
  rw [hp]
  simp

/-- **The reply stands.** -/
theorem headMergeLeavesReply : HeadMergeLeavesReply := by
  refine ⟨fun P s s' rs h => ?_, fun n s y h => ?_⟩
  · have e := (leavesSeven P s rs [] s' h).2.2.2.2.2.1
    unfold ProofFile.sameReply
    rw [e]
    exact beq_self_eq_true _
  · obtain ⟨cls, s₃⟩ := y
    obtain ⟨a, wo, G, _, _, e, _⟩ := claim_inv h
    unfold ProofFile.sameReply
    rw [show (cls, s₃).2 = s₃ from rfl, e]
    exact beq_self_eq_true _

/-- **The kind's block as it stands alone at a seat is that block without the guard.** -/
theorem headMergeSeated : HeadMergeSeated := by
  intro P name a
  refine Block.Still.guarded_eq ⟨fun _ t rs gs s' h => ?_, fun c hc n t y hy => ?_, fun c hc => ?_⟩
  · have h' : ((headClaimMergeKind P).decide t rs gs).bind (fun u =>
               match u.failed with
               | none => .ok u
               | some m => .error ("marked: " ++ m)) = .ok s' := h
    cases h0 : (headClaimMergeKind P).decide t rs gs with
    | error e =>
      rw [h0] at h'
      cases h'
    | ok u =>
      rw [h0] at h'
      have h'' : (match u.failed with
        | none => (.ok u : Except String S)
        | some m => .error ("marked: " ++ m)) = .ok s' := h'
      cases hf : u.failed with
      | none =>
        rw [hf] at h''
        rw [← Except.ok.inj h'']
        exact headMergeLeavesReply.1 P t u rs h0
      | some m =>
        rw [hf] at h''
        cases h''
  · have hc' : c ∈ [("the merge", headMergeClaim)] := hc
    rw [List.mem_singleton.1 hc'] at hy
    exact headMergeLeavesReply.2 n t y hy
  · cases hc

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeRecs
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeLeavesReply
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeSeated
