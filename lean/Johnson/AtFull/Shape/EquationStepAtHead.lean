-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/EquationStepAtHead.lean: the sub-protocol without a round "K9: the one
equation" of the proof file's own first chain, at all 25 links: under the head at which the
library's laws on that chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): one step on the shape of
the chain's state, with the laws "carries" and "returns" at the seated member's own decision. A
joining of laws; nothing is evaluated.

  `oneGS`: the step at the seat: no mark of failure; then oneG
    (Johnson/Desc/First/Batch/Shape/DoorChain.lean).
  **`equation_step_at`**: at l < 25 there are a link L of the chain and a member b of the chain's
    flat list, at number 14 l + (the number of L's hearing sub-protocols) + 4: b's decision carries
    oneGS; and it accepts wherever oneGS returns at the state's shape AND OneRest HOLDS AT THE
    STATE.

Limits. OneRest (DoorChain.lean) IS A PREMISE AT THE STATE: four tests on sizes that are not yet on
shapes, that the statement has the link's group, four tests on values, and that the slots in use are
told. The member's number hangs on L (Numbers.lean: 14 l + 11; 349 at l = 24); that b has no round
is not in the statement. "Carries" is under the step's own return. UNDER THE HEAD: that it has a
member is shown at two triples of files alone, in a side library. That oneGS returns at a shape that
the chain reaches is not shown. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.EquationAtHead
import Johnson.Desc.First.Batch.Shape.DoorChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **The step at the seat.** -/
def oneGS (a : ChainSh) : Except String ChainSh :=
  if a.marked then .error "a mark of failure" else oneG a

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem equation_step_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl), cF.links[l]? = some L ∧
      cF.blocksInOrder[14 * l + L.hear.length + 4 + 0]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t → oneGS (chainSh s) = .ok u → u = chainSh t) ∧
      ∀ s rs gs u, oneGS (chainSh s) = .ok u → OneRest s → ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨L, b, p, eL, eb, hy⟩ := equation_at h l hl
  refine ⟨L, b, eL, eb, fun s rs gs t u hd hg => ?_, fun s rs gs u hg hR => ?_⟩
  · unfold oneGS at hg
    cases hm : (chainSh s).marked with
    | true => rw [hm] at hg; exact nomatch hg
    | false =>
      rw [hm] at hg
      exact one_carries p s t rs gs u ((hy s t rs gs).1 hd).1 hg
  · unfold oneGS at hg
    cases hm : (chainSh s).marked with
    | true => rw [hm] at hg; exact nomatch hg
    | false =>
      rw [hm] at hg
      obtain ⟨t, ht⟩ := one_returns (Cl := Unit) p s rs gs u hg hR
      have hf : s.failed = none := by
        have : s.failed.isSome = false := hm
        simpa using this
      exact ⟨t, (hy s t rs gs).2 ⟨ht, hf⟩⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.equation_step_at
#print axioms Johnson.AtFull.Shape.oneGS
