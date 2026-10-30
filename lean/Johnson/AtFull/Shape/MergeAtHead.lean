-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/MergeAtHead.lean: the merge of the claims on the weights (the kind K11) at its
seat in the proof file's own first chain (member 346 of the flat list: the head's link's ninth
place): one step on the chain's shape, with both laws at the seated block's own decision. Under the
head `P5J.AtMgA`; a joining of laws; nothing is evaluated.

Main names.
* `mergeG P`: the step: where the kind's test on the shape accepts (`mergeGuardB P`,
  Johnson/Desc/K11/Shape/StepStatement.lean: it holds "no mark" itself), the kind's update
  (`mergeUpd P`); else nothing.
* `merge_at`: with Bs what the maker's own `ProofFile.baseOf` returns at the public part, and P the lot's
  numbers `K11.parOf Zp Bs.G₀`: the member b at number 346 of cF.blocksInOrder has the kind's own declared
  rounds, and, at rounds rs that pass the step's own test on their form, shown without the sealed
  digest as a step shows them: where b says yes and `mergeG P` returns at the state's shape, it
  returns the shape behind; and where `mergeG P` returns at the state's shape, b says yes.

How. `headMergeAtFull` (Johnson/Desc/K11/Exchange/AtFull.lean: which term stands at number 346),
`IM.yes_alone` (Johnson/IMR/SeatForm.lean), `mergeCarries` and `mergeReturns`
(Johnson/Desc/K11/Shape/Step.lean), `leavesSeven` (Johnson/Top/H0/MergeLaw/Law.lean: the decision
leaves the mark and what goes out).

Limits. The first law asks, beside the yes, that the step returns: that a yes gives the test's yes
is not shown. Both laws stand at rounds that fit: that is the frame's test, paid nowhere here. The
decision alone: the member's run of claims is not here. The kind tests no value. The head is handed
whole to headMergeAtFull; the letters Z, D, r, Np and x stand in no conclusion. The step returns an
Option, where the draw's and the seal's return an Except. No state is shown at which `mergeG P`
returns. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K11.Shape.Step
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.Top.H0.MergeLaw.Law
import Johnson.IMR.SeatForm
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide)
open Johnson.Desc.First.ForkMerge.ShapeStep (mergeGuardB mergeUpd mergeCarries mergeReturns)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **The step.** -/
def mergeG (P : HeadMergeP) (a : ChainSh) : Option ChainSh :=
  if mergeGuardB P a then some (mergeUpd P a) else none

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The merge at its seat (member 346)**: the kind's own declared rounds; and at rounds that fit:
a yes AND the step's return give the shape behind; the step's return gives a yes. -/
theorem merge_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.blocksInOrder[346]? = some b ∧
      b.rounds = (headClaimMergeKind (K11.parOf Zp Bs.G₀)).rounds ∧
      (∀ s rs gs t u, roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok t →
        mergeG (K11.parOf Zp Bs.G₀) (chainSh s) = some u → u = chainSh t) ∧
      ∀ s rs gs u, roundsFit b.rounds rs = true →
        mergeG (K11.parOf Zp Bs.G₀) (chainSh s) = some u →
        ∃ t, b.decide s (rs.map noDigest) gs = .ok t := by
  obtain ⟨Bs, Lk, name, hB, -, -, -, -, q, -⟩ :=
    Johnson.Desc.First.ForkMerge.Exchange.headMergeAtFull Z D r Zp Np cF x h
  have la : IM.LaidAlone ProofFile.sameReply
      (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Zp Bs.G₀)) name IM.k11Place)
      (headClaimMergeKind (K11.parOf Zp Bs.G₀)) name IM.k11Place := rfl
  have hy := IM.yes_alone la (by intro k; cases k)
  have hr := IM.alone_rounds la
  refine ⟨Bs, _, hB, q, hr, fun s rs gs t u hf hd hg => ?_, fun s rs gs u hf hg => ?_⟩
  · rw [hr] at hf
    have hd' : headMergeDecide (K11.parOf Zp Bs.G₀) s (rs.map noDigest) = .ok t :=
      ((hy s t _ gs).1 hd).1
    unfold mergeG at hg
    split at hg
    · rename_i hG
      rw [← mergeCarries _ rs s t hf hd' hG]
      exact (Option.some.inj hg).symm
    · cases hg
  · rw [hr] at hf
    unfold mergeG at hg
    split at hg
    · rename_i hG
      obtain ⟨t, ht⟩ := mergeReturns _ rs s hf hG
      have ht' : (headClaimMergeKind (K11.parOf Zp Bs.G₀)).decide s (rs.map noDigest) gs = .ok t := ht
      obtain ⟨-, -, -, k4, -, k6, -⟩ :=
        VerifiableInference.Desc.First.MergeLaw.leavesSeven _ s _ gs t ht'
      have hm : (chainSh s).marked = false := by
        have g := hG
        unfold mergeGuardB at g
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at g
        exact g.1.1.1
      have hs : s.failed = none := by
        have h2 : s.failed.isSome = false := hm
        simpa using h2
      refine ⟨t, (hy s t _ gs).2 ⟨ht', k4.trans hs, ?_⟩⟩
      unfold ProofFile.sameReply
      rw [k6]
      exact beq_self_eq_true _
    · cases hg

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.merge_at
#print axioms Johnson.AtFull.Shape.mergeG
