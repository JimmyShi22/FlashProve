-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RunsFront.lean: FOUR OF THE SEVEN RUNS OF CLAIMS OF THE HEAD's SEGMENT THAT
ARE NOT THE OUTPUT HEAD's OWN LEAVE WHAT THE HEAD HAS HEARD AS IT WAS, AND, WHERE THE LEDGER HAS ITS
SIZES, HAND ON A LATER ONE. Lemmas ON THE VERIFIER's TEXT, over the library alone; no prover is in
this file, and no goal is stated.

  `rests_frontSix`  what `AlikeFront` compares beside the ledger (`frontSix`,
                    Johnson/Desc/First/Link/Law/FrontStays.lean) rests under the four writings of
                    `FieldRests` (KeepsAny.lean there)
  `merge_frontLater`, `k8Run_frontLater`, `idle0_frontLater`   the merge's run, the run
                    "K8.equations" and the run that hands the state back give `FrontLater`
                    (K6HeardAtBatch.lean there) from the state in front to the state handed back
  `four_runs_frontLater`   **so do the runs that stand at (8, "the merge"), (5, "K8.equations"),
                    (2, "guests") and (7, "guests") of a link with the library's ties**
                    (`HeadTies`, PayHead.lean there)

Limits. IMPLICATIONS FROM A RUN's RETURN; the last from `HeadTies`, a premise: that a link has the
ties is not shown here. NOTHING ON THE LOOKUPS' THREE RUNS, (2, "objects"), (2, "planes") and (7,
"objects"). Nothing on the output head's own four runs. (The eleven entries of the head's segment's
order: `orderCuts`, Johnson/Desc/First/Driver/Chain.lean.)
Nothing on what a run claims. Called: `putTl_front`, `putFork_front` (FrontStays.lean),
`merge_keeps`, `k8Run_keeps` (KeepsAny.lean), `claim_inv` (Johnson/Top/H0/MergeLaw/Run.lean),
`OnBytes.PscRun.hideRun_keeps` (OnBytes/Tie/Pv/Psc/PscLater.lean), `k8Run_ok`
(Johnson/Desc/First/Batch/Law/K8Run.lean), `eq_later`
(Johnson/Desc/First/TailClaims/EquationsLater.lean), `S.fork_putTl`, `S.fork_putFork`
(Johnson/Desc/First/StateLedger.lean), `laterZ_refl` (LaterStretch.lean).
Nothing on any property.

-/
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.Desc.First.Link.Law.KeepsAny
import Johnson.Desc.First.Link.Law.PayHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Five
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open VerifiableInference.Desc.First.TailClaims.Law (eq_later)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K9L (k8Run k8Run_ok)
open VerifiableInference.Desc.LinkJoin

/-- What `AlikeFront` compares beside the ledger rests under the four writings. -/
theorem rests_frontSix : FieldRests frontSix where
  tl := putTl_front
  fork := putFork_front
  wrote e a G e₁ hw := by
    obtain ⟨h1, rfl⟩ := hw
    simp [frontSix, h1]
  head s a G h := by
    simp [frontSix, h]

/-- The merge's run. -/
theorem merge_frontLater (n : Nat) (e : S) (c : List Claim) (e₁ : S)
    (hr : headMergeClaim n e = .ok (c, e₁)) : FrontLater e e₁ := by
  refine ⟨merge_keeps rests_frontSix n e c e₁ hr, fun F hF _ => ?_⟩
  obtain ⟨a, wo, G, h1, _, rfl, _, hG⟩ := claim_inv hr
  have hF' : (if a.opened then some a.F else none) = some F := by
    simpa [S.fork?, h1] using hF
  by_cases ho : a.opened = true
  · rw [if_pos ho] at hF'
    obtain rfl : a.F = F := Option.some.inj hF'
    exact ⟨G, by simp [S.fork?, ho], OnBytes.PscRun.hideRun_keeps hG⟩
  · rw [if_neg ho] at hF'
    exact nomatch hF'

/-- The run "K8.equations". -/
theorem k8Run_frontLater (front : Nat) (e e₁ : S) (c : List Claim)
    (h : k8Run.2 front e = .ok (c, e₁)) : FrontLater e e₁ := by
  refine ⟨k8Run_keeps rests_frontSix front e e₁ c h, fun F' hF' _ => ?_⟩
  obtain ⟨F, tl, funs, tl', F1, hF, _, _, heq, rfl⟩ := k8Run_ok front e e₁ c h
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  exact ⟨F1, S.fork_putFork _ F F1 ((S.fork_putTl e tl').trans hF), eq_later heq⟩

/-- The run that returns no claim and hands the state back. -/
theorem idle0_frontLater (n : Nat) (e : S) (c : List Claim) (e₁ : S)
    (h : idle0 n e = .ok (c, e₁)) : FrontLater e e₁ := by
  obtain rfl : e = e₁ := congrArg Prod.snd (Except.ok.inj h)
  exact ⟨rfl, laterZ_refl e⟩

/-- **THE FOUR RUNS, AT A LINK WITH THE LIBRARY's TIES.** -/
theorem four_runs_frontLater {L : Link S Claim} {h : OnBytes.Model.Head.Shape}
    {iU3 l piece : Nat} {p : Par} {nU : Array Nat} (T : HeadTies L h iU3 l piece p nU) :
    ∀ o ∈ [(8, "the merge"), (5, "K8.equations"), (2, "guests"), (7, "guests")],
      ∀ run, At L o run → ∀ m t z, run m t = .ok z → FrontLater t z.2 := by
  intro o ho run hr m t z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact merge_frontLater m t z.1 z.2 (T.tMerge run hr m t z.1 z.2 hz)
  · exact k8Run_frontLater m t z.2 z.1 (T.tEq run hr m t z.1 z.2 hz)
  · exact idle0_frontLater m t z.1 z.2 (T.tGuests 2 (by simp) run hr m t z.1 z.2 hz)
  · exact idle0_frontLater m t z.1 z.2 (T.tGuests 7 (by simp) run hr m t z.1 z.2 hz)

end VerifiableInference.Desc.Kinds.Head.Law.Five

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.rests_frontSix
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.merge_frontLater
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.k8Run_frontLater
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.idle0_frontLater
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.four_runs_frontLater
