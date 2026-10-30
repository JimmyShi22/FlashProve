-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunCarries.lean: the merge's run of claims carries: what a lookup has heard
stands, and the ledger only grows, with its sizes. Theorems with their proofs.

The frame's laws on a link's claims (Johnson/Desc/First/LedgerAtFo.lean) ask of each run of claims
that it steps in `CarriesFo S.fork? hd`, at a reading hd of what a lookup has heard. Here that is
shown of the kind's one run, `headMergeClaim` (Johnson/Desc/First/Fork/MergeKind.lean).

Main names:
  `run_carries`: at every reading hd that does not see the head's ledger: where the run says yes
  from
    s to y.2: `CarriesFo S.fork? hd s y.2`. By `claim_inv` (Run.lean: of the record the head's
    ledger
    alone turns), the library's `hideRun_keeps` and `carriesFoOfLater`.
  `run_carries_look`: at `S.lookHeard?`, the reading of the lookup on the calls.
  `run_carries_digits`: at `fun s => s.tl?.bind (·.heard)`, the reading of the lookup on the digits.

Limits. A law on one run's text: no random step. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Run
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim CarriesFo carriesFoOfLater)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

/-- **The run carries**, at every reading that does not see the head's ledger. -/
theorem run_carries (hd : S → Option Forest.Heard)
    (hhd : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
      hd { s with here := .head { a with F := G } } = hd s)
    (n : Nat) (s : S) (y : List Claim × S) (h : headMergeClaim n s = .ok y) :
    CarriesFo S.fork? hd s y.2 := by
  obtain ⟨cls, s'⟩ := y
  obtain ⟨a, wo, G, h1, _, h2, _, h4⟩ := claim_inv h
  refine carriesFoOfLater _ _ _ _ ?_ ?_
  · intro g hg
    show hd s' = some g
    rw [h2, hhd s a G h1]
    exact hg
  · intro F hF
    show ∃ G', S.fork? s' = some G' ∧ OnBytes.PscRun.Later F G'
    unfold S.fork? at hF
    rw [h1] at hF
    by_cases ho : a.opened = true
    · simp only [ho, if_true] at hF
      refine ⟨G, ?_, ?_⟩
      · rw [h2]
        show (if a.opened = true then some G else none) = some G
        rw [if_pos ho]
      · rw [← Option.some.inj hF]
        exact OnBytes.PscRun.hideRun_keeps h4
    · simp [ho] at hF

/-- At the reading of the lookup on the calls. -/
theorem run_carries_look (n : Nat) (s : S) (y : List Claim × S)
    (h : headMergeClaim n s = .ok y) : CarriesFo S.fork? S.lookHeard? s y.2 :=
  run_carries _ (fun s a G hs => by simp [S.lookHeard?, hs]) n s y h

/-- At the reading of the lookup on the digits. -/
theorem run_carries_digits (n : Nat) (s : S) (y : List Claim × S)
    (h : headMergeClaim n s = .ok y) :
    CarriesFo S.fork? (fun s => s.tl?.bind (·.heard)) s y.2 :=
  run_carries _ (fun s a G hs => by simp [S.tl?, hs]) n s y h

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.run_carries
#print axioms VerifiableInference.Desc.First.MergeLaw.run_carries_look
#print axioms VerifiableInference.Desc.First.MergeLaw.run_carries_digits
