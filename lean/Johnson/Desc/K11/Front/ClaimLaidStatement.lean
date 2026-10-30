-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/ClaimLaidStatement.lean: IN FRONT OF THE MERGE A CLAIM IS LAID: at every
state that is reached at border 346 of the first chain's flat list by the sub-protocols' own steps,
under the library's hypothesis on the public files (`P5J.AtMgA`) at the full size; AND NOTHING WAITS
THERE, where the promise's test on where the chain stands accepts: STATEMENTS ALONE: two definitions
of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are
lemmas' statements.

Why. The library's condition on the state in front of the merge (`WaK6`,
Johnson/Desc/Kinds/Law/WtJointAt.lean) and `FrontOfMergeRaw`
(Johnson/Desc/ProofFile/Honest/K11/ClaimBareStatement.lean, a file that is not in this library) say
of the claim: "the one that lies there, IF one lies there, is what the description's function
makes". That one lies there is a premise of the kind's laws ("the state is ready").

  `ClaimLaidRaw`      the state stands in the head's link, which is open; the covered positions,
                      what the head heard and the head's tables are had; A CLAIM IS LAID; and it is
                      what `weightsClaim` makes of these
  `NoneWaitsOfShape`   shapeAt at the written lists and border 346 gives s.noneWaits = true

Limits. "Reached" is a premise: that any state is reached is not said. The hypothesis is a premise;
it stands at the earlier hash. That the claim fits the layout is not said. Nothing on any property.
-/
import Johnson.Desc.Kinds.Law.WtJointAt
import Johnson.Desc.Sound.MgAt.K11Closed
import Johnson.P5J.MgAtAll
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (linksFull psFull)
open VerifiableInference.Desc.First (S HeadOwn shapeAt)
open VerifiableInference.Desc.Kinds.Head.Law (runAt)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The statement that a claim is laid. Not proved here; a lemma's statement, none of the library's
goals. -/
def ClaimLaidRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF : S),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    ∃ (a : HeadOwn) (cov : Head.Covered) (x : Head.Heard) (t : Head.Tables) (claim : WsClaim),
      sF.here = .head a ∧ a.opened = true ∧ sF.covered Bs.G₀.W.T Bs.G₀.W.P.h.V = .ok cov ∧
      a.x = some x ∧ a.t = some t ∧ a.claim = some claim ∧
      VerifiableInference.Desc.First.Look.weightsClaim (runAt Bs.G₀.W cov x t)
        Bs.G₀.W.layers.wsLay = .ok claim

/-- The statement that nothing waits. Not proved here; a lemma's statement, none of the library's
goals. -/
def NoneWaitsOfShape : Prop :=
  ∀ s : S, shapeAt linksFull psFull[346]? s = true → s.noneWaits = true

end Johnson.Desc.First.ForkMerge.Front

#print axioms Johnson.Desc.First.ForkMerge.Front.ClaimLaidRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.NoneWaitsOfShape
