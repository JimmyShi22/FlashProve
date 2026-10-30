-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/HeadJoins.lean: THE JOINS AT THE GOALS' TWO NAMED SETS OF PUBLIC FILES (VerifierAndGoals.storedPublicFiles,
VerifierAndGoals.zGap): THE HEAD HAS A MEMBER THERE AT WHICH FIFTEEN FURTHER NAMED CONDITIONS HOLD TOGETHER.
NO PREMISE BUT THAT THE FILES ARE ONE OF THE TWO. One theorem; no definition; one call a set of
files.

  - headJoins_named: hZ : VerifierAndGoals.NamedFiles Z ⊢ protocolDataWellFormed accepts at asDescriptionFiles Z; rowsRead Z; and the
    whole of P5J.headJoins_of_live (Johnson/P5J/HeadJoinsOfLive.lean, whose head tells the fifteen
    one by one). Scope and reading: VerifierAndGoals.filesRead.full, .other. protocolDataWellFormed: theLive_zFull
    (AtFullSide/Top/LiveAtFull.lean), theLive_zGap (LiveAtPolicies.lean).

What it is for. AtFullSide/Top/HeadMemberAtFull.lean says among its limits: "WHICH HEAD: P5J.AtMgA
(and the AtMg that it extends): not AtMgR ..., and none of the other named conditions that a law
takes beside the head". For the fifteen named here that limit is overtaken: a law of the library
that speaks under the head AND one or more of these is not empty at these files for want of them.

Why here. protocolDataWellFormed's accept at these files stands over closed facts that want a larger thread stack:
the side library. Nothing under lean/Johnson/ imports it.

Limits. AT THE EARLIER HASH OnBytes.secondHashFunction ALONE, a fixed function. The member is no proof and no
request: Zp, Np, cF and x are what the makers return at the public files. An accept of protocolDataWellFormed is no
sign that the verifier accepts any proof. rowsRead FOLLOWS FROM protocolDataWellFormed, NOT FROM THE HEAD.
KindsLaws' FIELD k12 IS ITSELF AN IMPLICATION (H2K12.LastTypedAt ... → ...): THE JOIN DOES NOT PAY
ITS PREMISE. It proves that premises can be met together; it adds nothing to what follows from them.
NO SOUNDNESS FOLLOWS FROM A MEMBER. A MEMBER STANDS AT secondHashFunction, AT THE TWO WRITTEN SETS OF FILES, IN
THE SIDE LIBRARY: NO MORE. VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap are terms written in Ladder/Stored.lean: no
Lean code ties them to the package's folder examples/; the example's weights are synthetic. At the
constant fixedConfigurationDigest in the digest's place, not at the digest of these files. The closed facts beneath
are proved by evaluation in Lean's kernel, and have been checked by that kernel alone: no
independent checker has replayed them. IT CAN BREAK UNSEEN: it stands over the makers' texts as they
are; since nothing in the library proper imports this file, only a build of the side library shows a
break. It names goal-like definitions (KindsConds, KindsLaws); it states no goal.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.HeadJoinsOfLive
import AtFullSide.Top.HeadMemberAtGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open VerifiableInference.PlanWritten (madePinnedAt cutOf cutFirstFull madeRow)
open _root_.Desc.K14.Law (seatZ secondAt)
open VerifiableInference.Desc.First (fenceFit)
open P5J (fullLinks)
open H2K5.Door (PadsAll K5CondAt K5Along)
open VerifiableInference.Desc.Sound (frameAt allOf)
open OnBytes.Slice (frS)
open OnBytes.Road.K4 (K4Last K4Owes K4Cond)
open VerifierAndGoals.AtTheName (KindsConds KindsLaws)

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap

/-- **AT EACH OF THE GOALS' TWO NAMED SETS OF PUBLIC FILES THE HEAD HAS A MEMBER AT WHICH THE
FIFTEEN HOLD TOGETHER.** rowsRead follows from protocolDataWellFormed, not from the head. KindsLaws' field k12 is
itself an implication, whose premise the join does not pay. At the earlier hash secondHashFunction alone. -/
theorem headJoins_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true ∧ P5J.rowsRead Z ∧
    ∃ Zp Np cF x, ∃ h : P5J.AtMgA OnBytes.secondHashFunction Z (VerifierAndGoals.AtTheName.dpZ Z)
        (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles Z)) Zp Np cF x,
      -- (1) the pins, in both sealed forms
      (madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true ∧
        cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull) ∧
      (madeRow Zp = true ∧ cutOf cF.blocksInOrder = cutFirstFull) ∧
      -- (2) the opening
      (∃ Bs base, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs
        base cF (seatZ Zp Np) (secondAt Zp Np) ∧ Bs.G₀.W = P5J.At.X Zp) ∧
      -- (4) the table's test · (9) offC · (8) PadsAll
      fenceFit (P5J.At.N Zp cF) fullLinks P5J.At.ps = true ∧ h.toAtMg.offC = true ∧ PadsAll h ∧
      -- (5) (6) (7) the list of seats is laid; K5's two named conditions at it
      (∃ L, P5J.At.laid? Zp = some L ∧ K5CondAt h L ∧
        K5Along (Fr := frameAt ((VerifierAndGoals.AtTheName.dpZ Z).at frS.P.T.a)
            (allOf ((VerifierAndGoals.AtTheName.dpZ Z).at frS.P.T.a))
            ((VerifierAndGoals.AtTheName.dpZ Z).at frS.P.T.a).key₁ 0)
          h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent) ∧
      -- (10) K4's three
      K4Last h ∧ (∃ L, K4Owes h L) ∧ (∀ Pp, ∃ L, K4Cond h L Pp) ∧
      -- (11) (12) K9's two and K1's, at every 𝔏
      (∀ 𝔏, h.K9LastC 𝔏 ∧ h.K9LeftC 𝔏 ∧ h.K1Cond 𝔏) ∧
      -- (14) the facts along the reached states
      (∃ L, P5J.AtMgR OnBytes.secondHashFunction Z (VerifierAndGoals.AtTheName.dpZ Z)
        (FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles Z)) Zp Np cF h.toAtMg.rch (fun a => a.1) L) ∧
      -- (15) (16) K11's at the head's own 𝔏; the two records of the skeleton
      h.K11Cond h.free ∧ KindsConds h h.free ∧ KindsLaws h h.free := by
  -- the three premises first, at the named files; the long statement is then met at the letter Z
  have key : VerifierAndGoals.InScope Z = true ∧ (∃ pp, VerifierAndGoals.readFiles Z = .ok pp) ∧
      FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true := by
    rcases hZ with rfl | rfl
    · obtain ⟨scope, pp, read, _⟩ := VerifierAndGoals.filesRead.full
      exact ⟨scope, ⟨pp, read⟩, theLive_zFull⟩
    · obtain ⟨scope, pp, read, _⟩ := VerifierAndGoals.filesRead.other
      exact ⟨scope, ⟨pp, read⟩, theLive_zGap⟩
  obtain ⟨scope, ⟨pp, read⟩, hl⟩ := key
  exact ⟨hl, P5J.headJoins_of_live Z scope read hl⟩

end AtFullSide.Top

#print axioms AtFullSide.Top.headJoins_named
