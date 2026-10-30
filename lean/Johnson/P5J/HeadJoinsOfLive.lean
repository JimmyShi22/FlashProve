-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/HeadJoinsOfLive.lean: THE JOINS: AT EVERY SET OF PUBLIC FILES IN SCOPE THAT READS AND AT
WHICH THE TEST protocolDataWellFormed ACCEPTS, THE HEAD (P5J.AtMgA) HAS A MEMBER AT WHICH FIFTEEN FURTHER NAMED
CONDITIONS HOLD TOGETHER. One theorem; no definition; calls alone.

What it is for. Many laws of the library take, beside the head, a further named condition (the pins,
the opening, fenceFit, K5CondAt, K4Last, K9LastC, K1Cond, AtMgR along the reached states, ...), and
their comments say that no member of that whole is known. EACH OF THESE CONDITIONS FOLLOWS FROM THE
HEAD BY A THEOREM THAT LIES. Here they are joined AT ONE MEMBER: any part of the whole follows by
projections.

  - headJoins_of_live: scope, read, hl (P5J.head_of_live's three premises) ⊢ rowsRead Z, and Zp, Np,
    cF, x, h with: (1) the pins, in both forms (pins_of_laid, pins_at_head) · (2) the opening
    (open_all) · (4) fenceFit (AtMg.fence) · (9) offC (offC_head) · (8) PadsAll (pads_of_head) · (5)
    (6) (7) a laid list of seats L (laid_of_head) with K5CondAt and K5Along at it (k5CondAt_at_head,
    k5Along_at_head) · (10) K4Last, K4Owes, K4Cond (k4Last_of_head, k4Owes_of_last, k4Cond_of_last)
    · (11) (12) at every 𝔏: K9LastC, K9LeftC, K1Cond (k9LastC_at_head, k9LeftC_of_last,
    k1Cond_of_head) · (14) AtMgR along the reached states (atMgR_rch_of_head) · (15) K11Cond at the
    head's own 𝔏 (k11CondAll_free) · (16) KindsConds and KindsLaws there (kindsConds_at_head,
    kindsLaws_at_head). The numbers are those of the sheet on which the statement was read before it
    was typed; (3) is rowsRead; (13), K2Told, is a theorem outright (k2Told_paid) and wants no join.

AN IMPLICATION: that protocolDataWellFormed accepts at any files is not said here: at the two written sets of files
it is proved in the side library (AtFullSide/Top/HeadJoins.lean draws the end there).

Limits. AT THE EARLIER HASH OnBytes.secondHashFunction ALONE, a fixed function. The member is no proof and no
request: Zp, Np, cF and x are what the makers return at the public files. An accept of protocolDataWellFormed is no
sign that the verifier accepts any proof. rowsRead FOLLOWS FROM protocolDataWellFormed, NOT FROM THE HEAD.
KindsLaws' FIELD k12 IS ITSELF AN IMPLICATION (H2K12.LastTypedAt ... → ...): THE JOIN DOES NOT PAY
ITS PREMISE. It proves that premises can be met together; it adds nothing to what follows from them.
NO SOUNDNESS FOLLOWS FROM A MEMBER. It names goal-like definitions (KindsConds, KindsLaws:
Johnson/Goal/Skeleton/); it states no goal.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.HeadOfLive
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.Desc.First.Att.Door.Law.K5AtConstant
import Johnson.Desc.First.Att.Door.Law.K5KindWhole
import Johnson.Desc.First.Att.Door.Law.K5AlongOfHead
import Johnson.Desc.First.Att.Door.Law.K5PadsOfHead
import Johnson.Top.H0.K2Ties.OffHead
import Johnson.P5T.FenceAtMg
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K04OfHead
import Johnson.Road.K4.K04Last
import Johnson.P5J.K09EndC
import Johnson.P5J.K09LastC
import Johnson.Desc.AtSeats.K01CondOfHead
import Johnson.P5J.StartAtHead
import Johnson.K11R.KindAtFree
import Johnson.Goal.Skeleton.KindsCondsAtHead
import Johnson.Goal.Skeleton.KindsLawsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.PlanWritten (madePinnedAt cutOf cutFirstFull madeRow)
open _root_.Desc.K14.Law (seatZ secondAt)
open VerifiableInference.Desc.First (fenceFit)
open P5J (fullLinks)
open H2K5.Door (PadsAll K5CondAt K5Along)
open VerifiableInference.Desc.Sound (frameAt allOf)
open OnBytes.Slice (frS)
open OnBytes.Road.K4 (K4Last K4Owes K4Cond)
open VerifierAndGoals.AtTheName (KindsConds KindsLaws)

/-- **THE HEAD HAS A MEMBER AT WHICH THE FIFTEEN HOLD TOGETHER, WHEREVER protocolDataWellFormed ACCEPTS.** rowsRead
follows from protocolDataWellFormed, not from the head. KindsLaws' field k12 is itself an implication, whose
premise the join does not pay. At the earlier hash secondHashFunction alone. -/
theorem headJoins_of_live (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : VerifierAndGoals.InScope Z = true)
    (read : VerifierAndGoals.readFiles Z = .ok pp) (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    P5J.rowsRead Z ∧
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
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_of_live Z scope read hl
  obtain ⟨L, hL⟩ := OnBytes.Road.K4.laid_of_head h.toAtMg
  have hp := P5J.pins_of_laid h.scope h.laid
  have h4 := OnBytes.Road.K4.k4Last_of_head h
  exact ⟨(P5J.owed_of_live hl).rows, Zp, Np, cF, x, h, hp, H2K5.Door.pins_at_head h.toAtMg,
    H2K5.Door.open_all h, h.toAtMg.fence,
    VerifiableInference.Desc.First.K2Ties.offC_head h.toAtMg hp.1, H2K5.Door.pads_of_head h,
    ⟨L, hL, H2K5.Door.k5CondAt_at_head h hL, H2K5.Door.k5Along_at_head h hL⟩, h4,
    OnBytes.Road.K4.k4Owes_of_last h4, fun _ => OnBytes.Road.K4.k4Cond_of_last h4,
    fun 𝔏 => ⟨P5J.k9LastC_at_head h 𝔏, P5J.k9LeftC_of_last h 𝔏 (P5J.k9LastC_at_head h 𝔏),
      P5J.k1Cond_of_head h 𝔏⟩,
    P5J.atMgR_rch_of_head h, K11.k11CondAll_free h, VerifierAndGoals.AtTheName.kindsConds_at_head h,
    VerifierAndGoals.AtTheName.kindsLaws_at_head h⟩

end P5J

#print axioms P5J.headJoins_of_live
