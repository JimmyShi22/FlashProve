-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/HandsConst.lean: the code switch (K2): THE FIELDS hHands AND hFk OF ITS
CONDITION AT THE COMPOSED MEANING's CONSTANT, AT THE CHAIN's OWN BLOCK AT EACH OF THE 25 PLACES,
FROM THE ONE HEAD (AtMg) AND NAMED TESTS ALONE. A join. A file beneath the condition.
A law file; no running text imports it.

OF HandsAtConst.lean AND HandsPaid.lean: their arms at the head's
place (339) and at the finish (353) end at the lot's BARE sub-protocol, not at the chain's own block
there, which is that sub-protocol seated. The step between the two stands in other files
(Johnson/IMR/: HandsR.under, HandsFence.lean; alone_underR, SeatForm.lean), and is laid in here.

  FkR Zp cF z k s   the fence: (z, s) is reached at border k of the first chain.
  fk_of_rchAt       the field hFk at that fence: «reached» at the description's first chain
                    (RchAt, Johnson/Top/H0/Walk/ReachAt.lean) IS the fence: by unfolding.
  hHands_link_const   at k = 14 (m + 1) + 2, m < 23 · hHands_head_const at 339 · hHands_fin_const
                    at 353: ∀ b, cF.blocksInOrder[k]? = some b → ∀ z, HandsR (FkR Zp cF z) (h.𝔇 𝔇₀).N
                    P5J.fullLinks P5J.At.ps (EQ (mgAll (h.𝔇 𝔇₀) mgBase) … z) ft k b.
PAID HERE, AGAINST HandsPaid.lean's ARMS: the opening O (the head's field laid.opened) · hlot hpl hJ
(first_sits · chain_hear_alone · chain_back_any, as GrownJoin.lean's s1_of_shares spends them) ·
hFk (the fence is «reached») · hG (Open.blank) · the letter q₀ (out of k5PlanB's accept at segment
1).
WHAT STAYS: THE HEAD, AND SEVEN NAMED SENTENCES ON PUBLIC DATA: hy (madePinnedAt) · hcut (the
chain's blocks have the written cut) · hB (sendsAreB at 358, at the ground that is made for a
request of zeros) · linkPlanB at the place's segment · k5PlanB at segment 1 and, where the place's
segment is an attention's, there · headPlanB · hh (the head's plan has heard nothing:
Zp.p.X.H.tl.heard = none).
WHICH OF THESE A TEXT OF THE VERIFIER ASKS IS NOT SAID HERE. NO MEMBER: that they can be met
together is not shown here.
Limits. The full size alone. At secondHashFunction alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Ties.HandsPaid
import Johnson.IMR.GrownJoin
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)
open VerifiableInference.Desc.Sound (below mgAll mgBase MgData)
open P1K2 (EQ linkPlanB k5PlanB headPlanB k5Plan_of_B)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open IM (HandsR subW subAt)
open P5J (AtMg F0T)

/-- **The fence.** -/
def FkR (Zp : ProofFile.Pub) (cF : Chain P5J.TS ProofFile.Cl) (z : ProofFile.InstPub) (k : ℕ) (s : S) : Prop :=
  Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (z, s)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The field hFk.** -/
theorem fk_of_rchAt {Str : Type} {k : ℕ} {z : ProofFile.InstPub} {s : S} {y : Str}
    (u : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k ((z, s), y)) : FkR Zp cF z k s := u

variable (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok OnBytes.Flat.numsFull.rows
    (P5J.colsAt OnBytes.Flat.numsFull) nR (P5J.At.X Zp))

/-- **At the 23 places that open a segment's link.** -/
theorem hHands_link_const (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ →
      sendsAreB Zp.made.proof.1 358 (snAt Zp G₀ IM.placesW) = true)
    {m : ℕ} (h23 : m < 23)
    (hLP : linkPlanB Zp (h.𝔇 𝔇₀).pubD.nsOf (h.𝔇 𝔇₀).pubD.d3 (m + 1) = true)
    (hK1 : k5PlanB Zp (h.𝔇 𝔇₀).pubD.d5 Zp.first.layout 1 = true)
    (hK5 : subW (m + 1) = .attention →
      k5PlanB Zp (h.𝔇 𝔇₀).pubD.d5 Zp.first.layout (m + 1) = true) {ft : ℕ} :
    ∀ b, cF.blocksInOrder[14 * (m + 1) + 2]? = some b → ∀ z,
      HandsR (FkR Zp cF z) (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft (14 * (m + 1) + 2) b := by
  intro b hb z
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨q₀, -, -, -⟩ := k5Plan_of_B (D := (h.𝔇 𝔇₀).pubD) (N := (h.𝔇 𝔇₀).N) hK1 rfl
  have hk0 : (kindsBeforeBatching (subAt (m + 1)) (m + 1 == 0))[0]? = some KindName.K2 := by
    interval_cases m <;> rfl
  obtain ⟨Lk, b0, e1, e2, L, hL, b', hb', ep, hj⟩ :=
    IM.first_sits h.scope h.reads O (m + 1) (by omega) KindName.K2 hk0
  have hix := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega) 0] at hix
  obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
  exact hHands_link_paid h 𝔇₀ O hy hcut (hB _ O.blank) h23 (fun s hs => ⟨z, hs⟩) ⟨L, hL, hb'⟩ ep hj
    z q₀ hLP hK5

/-- **At the head's place.** -/
theorem hHands_head_const (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ →
      sendsAreB Zp.made.proof.1 358 (snAt Zp G₀ IM.placesW) = true)
    (hHP : headPlanB Zp (h.𝔇 𝔇₀).pubD.nsOf (h.𝔇 𝔇₀).pubD.d3 = true)
    (hh : Zp.p.X.H.tl.heard = none) {ft : ℕ} :
    ∀ b, cF.blocksInOrder[339]? = some b → ∀ z, HandsR (FkR Zp cF z) (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft 339 b := by
  intro b hb z
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hk1 : (kindsBeforeBatching (subAt 24) (24 == 0))[1]? = some KindName.K2 := rfl
  obtain ⟨h9, h10⟩ := IM.hear_kinds_plain hk1
  obtain ⟨Lk, b0, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain 24 (subAt 24)
      (IM.subs_scope h.scope h.reads O 24 (by omega)) 1 KindName.K2 hk1 h9 h10
      ⟨by omega, by omega⟩
  have hix := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega) 1] at hix
  obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
  exact (hHands_head_paid h 𝔇₀ O hy hcut (hB _ O.blank) (fun s hs => ⟨z, hs⟩) ⟨L, hL, hb'⟩ ep z
    O.blank (by rw [O.W]; exact hh) hHP).under (IM.alone_underR hla)

/-- **At the finish.** -/
theorem hHands_fin_const (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ →
      sendsAreB Zp.made.proof.1 358 (snAt Zp G₀ IM.placesW) = true) {ft : ℕ} :
    ∀ b, cF.blocksInOrder[353]? = some b → ∀ z, HandsR (FkR Zp cF z) (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft 353 b := by
  intro b hb z
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, hallB⟩ := IM.base_made O.made
  obtain ⟨several, hsev, -, hbk⟩ :=
    IM.chain_back_any hallB (IM.makers_K9 Zp Bs.G₀) O.places O.chain
  obtain rfl : several = true := hsev.2 (IM.base_has_K13 O)
  have hkj : (backKinds true)[0]? = some KindName.K2 := rfl
  obtain ⟨b0, e0, sp, -, L, hL, b', hb', -, ep, hla⟩ := hbk 0 KindName.K2 hkj (by decide)
  have hix := (IM.back_numbers h.scope h.reads O).1 0 b0 e0
  obtain rfl := Option.some.inj (hix.symm.trans hb)
  exact (hHands_fin_paid h 𝔇₀ O hy hcut (hB _ O.blank) (fun s hs => ⟨z, hs⟩) ⟨L, hL, hb'⟩ ep
    z).under (IM.under_bare (IM.alone_underR hla))

end Meaning.K2

#print axioms Meaning.K2.fk_of_rchAt
#print axioms Meaning.K2.hHands_link_const
#print axioms Meaning.K2.hHands_head_const
#print axioms Meaning.K2.hHands_fin_const
