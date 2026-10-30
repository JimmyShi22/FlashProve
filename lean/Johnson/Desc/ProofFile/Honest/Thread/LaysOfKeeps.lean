-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/LaysOfKeeps.lean: a rider clause of the first chain's invariant
is established by a sub-protocol (`LaysAtS`, Thread/SharesS.lean) if a relation `K` between the
state before and the state after holds at every accepting step, and `K` with the invariant before
the step gives the clause's fact after it. The column `hK` of `owesS_head_form`
(Thread/GatherHeadForm.lean) gives such a relation: the clause of `keeps` of the sub-protocol's
kind. No definition.

  1  `laysAtS_of_clause`   the general lemma, at any `Thread` and any `Said`
  2  `k3Head_fold1`   from the clause `K3KeepsHead` of the lookup on the digits of the output head's
     segment (K3/Law/Thread/K3Keeps.lean): if `tl.foldDrawn` is 0 before the step, it is 1 after it
  3  `k11_wo`   from the clause `K11Keeps` of the merge
     (Johnson/Desc/K11/Returns/KeepsStatement.lean): the field `wo` is set after the step
  4  `k4_own`   from the clause `K4KeepsM` (K4/Law/KeepsStep.lean): the segment's own rounds have
     returned something after the step

Three more facts of this sort are lemmas of the authors of the clauses: `K6Keeps.heard`
(Johnson/Desc/K6/Honest/Law/Keeps.lean), `k1_reads_lays_t` (K1/Law/KeepsReads.lean) and
`K8KeepsM.fold0_head` (Johnson/Desc/K8/Honest/KeepsFold.lean).

Limits.
  * Items 2 to 4 start from a clause. Nothing shows that a clause holds at any step.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.Desc.K11.Returns.KeepsStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **A clause is established by a sub-protocol whose accepting steps satisfy `K`.** `hK`: `K` holds
at every accepting step from the invariant. `hc`: the invariant before the step and `K` give the
clause's fact after the step. -/
theorem laysAtS_of_clause {b : Nat} {c : RiderCl W S} {K : S → S → Prop}
    (hK : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → K s s')
    (hc : ∀ k s m E s', ThrS T Said b k s m E → K s s' → c.prop (b + 1) m.st.input s') :
    LaysAtS T Said b c :=
  fun blk hblk k s m E ds y cols s' hA hd hS =>
    hc k s m E s' hA (hK blk hblk k s m E ds y cols s' hA hd hS)

end

open VerifiableInference.Desc.First (S)

/-- The lookup on the digits of the output head's segment counts one draw more. -/
theorem k3Head_fold1 {sh : OnBytes.Model.Forest.Shape} {s s' : S}
    (K : ProofFile.Honest.K3.Law.AtThr.K3KeepsHead sh s s')
    (h0 : ∀ a, s.here = .head a → a.tl.foldDrawn = 0) :
    ∃ a', s'.here = .head a' ∧ a'.tl.foldDrawn = 1 := by
  obtain ⟨-, tl, F, H, G, a₀, claim, htl, -, ha, ho, rfl, -⟩ := K
  have e0 := h0 a₀ ha
  have et : tl = a₀.tl := by
    unfold S.tl? at htl
    rw [ha] at htl
    simpa [ho] using htl.symm
  refine ⟨_, rfl, ?_⟩
  show tl.foldDrawn + 1 = 1
  rw [et, e0]

/-- After the merge the field `wo` is set. -/
theorem k11_wo {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {s s' : S}
    (K : Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    ∃ a', s'.here = .head a' ∧ a'.wo.isSome = true := by
  obtain ⟨⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩, -⟩ := K
  exact ⟨_, rfl, rfl⟩

/-- After K4's sub-protocol the segment's own rounds have returned something. -/
theorem k4_own {s s' : S} (K : ProofFile.Honest.K4.K4KeepsM s s') : ∃ o, s'.own? = some o := by
  obtain ⟨⟨-, a, G, o, -, -, ho, -⟩, -⟩ := K
  exact ⟨o, ho⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.laysAtS_of_clause
#print axioms ProofFile.Honest.k3Head_fold1
#print axioms ProofFile.Honest.k11_wo
#print axioms ProofFile.Honest.k4_own
