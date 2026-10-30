-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/HandsPaid.lean: the code switch (K2): THE FIELD hHands OF ITS CONDITION AT THE
COMPOSED MEANING's CONSTANT, AT EACH OF THE 25 PLACES (HandsAtConst.lean's three arms), WITH TWO
MORE PREMISES GONE: hgrp («the plan's number of the group is the place's») AND htok («the token is
small» rides over the head's switch). A join. A file beneath the condition.
A law file; no running text imports it.

  groupAt_const   the constant's numbers' groupAt is the identity: by unfolding (the layings
                  withRows, withTold leave that reader).
  hgrp_link_at · hgrp_fin_at   so hgrp, at a link (the head's among them) by
                  grp_of_id, at the finish by hgrp_finish_made
                  (Johnson/Top/H0/Tw/K2C/GroupAtNums.lean), whose premise «the sized request has 25
                  links» is Opts/PlannerRequestHas25Links.lean's pub_links: in scope, where the public part is
                  made: no test on the plan.
  tok_of_left     the public item «the token is small» reads the reply that the state holds, and
                  nothing else (tokenHeardB, Johnson/Stored/FillK6K7.lean): so it rides over every
                  step that leaves the field out (Left, Johnson/Top/H0/K2Ties/Left.lean).
  htok_at         so htok: the head's bare sub-protocol's accept leaves it (left_bare_hear,
                  Johnson/P1K2R/SharesE.lean).
  hHands_link_paid · hHands_head_paid · hHands_fin_paid   the three arms without the two.
WHAT STAYS IN FRONT, BY NAME: the head h : AtMg · the opening O · hFk · hlot hpl hJ · hy · hcut ·
hB · linkPlanB · k5PlanB (at attention's segments) · headPlanB · at the head: hG · hh · the letter
q₀.
NO MEMBER: that these can be met together is not shown here.
Limits. The full size alone. At secondHashFunction alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Ties.HandsAtConst
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Top.H0.Opts.PlannerRequestHas25Links
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc.Sound (below mgAll mgBase MgData)
open P1K2 (EQ prepOf numsAt linkPlanB k5PlanB headPlanB grp_of_id hgrp_finish_made left_bare_hear)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.First.K2Caller (pub_links)
open VerifiableInference.Desc.Kinds.Head (tokenHeardB)
open IM (HandsR Yes linksW placesW subW Joined)
open P5J (AtMg F0T)

/-- «The token is small» reads the reply alone. -/
theorem tok_of_left {Q : Type} (D : PubData) (bs : Pub → Q × S → Bool) (z : Q) {s s' : S}
    (e : s'.out = s.out) (h : pubAll D bs .tokenSmall (z, s) = true) :
    pubAll D bs .tokenSmall (z, s') = true := by
  have h' : tokenHeardB D.hShape D.iU3 s = true := h
  show tokenHeardB D.hShape D.iU3 s' = true
  unfold tokenHeardB at h' ⊢
  have t : VerifiableInference.Desc.Kinds.Reply.token
      (VerifiableInference.Desc.Kinds.Head.seatAt D.hShape D.iU3).toSeat s' =
      VerifiableInference.Desc.Kinds.Reply.token
        (VerifiableInference.Desc.Kinds.Head.seatAt D.hShape D.iU3).toSeat s := by
    show (s'.out.reply).map OnBytes.Desc.Reply.tokOf = (s.out.reply).map OnBytes.Desc.Reply.tokOf
    rw [e]
  rw [t]
  exact h'

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok OnBytes.Flat.numsFull.rows
    (P5J.colsAt OnBytes.Flat.numsFull) nR (P5J.At.X Zp))

theorem groupAt_const : (h.𝔇 𝔇₀).N.groupAt = id := rfl

theorem hgrp_link_at (G₀ : ProofFile.Ground) (l : ℕ) :
    ∀ P n, prepOf Zp G₀ = some P → numsAt P (some l) = some n →
      (h.𝔇 𝔇₀).N.groupAt l = n.grp :=
  fun _ _ _ hn => grp_of_id (groupAt_const h 𝔇₀) hn

theorem hgrp_fin_at (G₀ : ProofFile.Ground) :
    ∀ P n, prepOf Zp G₀ = some P → numsAt P none = some n → (h.𝔇 𝔇₀).N.groupAt 25 = n.grp :=
  hgrp_finish_made (P5J.At.pseats Zp) (P5J.At.shape Zp) P5J.At.links cF.blocksInOrder Zp G₀
    (pub_links h.scope h.laid.pub)

theorem htok_at {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {Fk : Nat → S → Prop} {ft : Nat} (z : ProofFile.InstPub) :
    ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll (h.𝔇 𝔇₀).pubD noPub .tokenSmall (z, s) = true →
      pubAll (h.𝔇 𝔇₀).pubD noPub .tokenSmall (z, s') = true :=
  fun _ _ _ hy _ _ e => tok_of_left _ _ z (left_bare_hear hlot hpl hy).out e

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the 23 places that open a segment's link.** -/
theorem hHands_link_paid
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true)
    {Fk : Nat → S → Prop} {m : ℕ} (h23 : m < 23)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s →
      ∃ z, Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ L.blocks Bs.G₀)
    (hpl : b'.place = { chain := 1, link := some (m + 1), piece := 1, kind := .K2 })
    (hJ : Joined Zp (m + 1) b b' { chain := 1, link := some (m + 1), piece := 1, kind := .K2 })
    {ft : Nat} (z : ProofFile.InstPub) (q₀ : Attention.Plan)
    (hLP : linkPlanB Zp (h.𝔇 𝔇₀).pubD.nsOf (h.𝔇 𝔇₀).pubD.d3 (m + 1) = true)
    (hK5 : subW (m + 1) = .attention →
      k5PlanB Zp (h.𝔇 𝔇₀).pubD.d5 Zp.first.layout (m + 1) = true) :
    HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft (14 * (m + 1) + 2) b :=
  hHands_link_at h 𝔇₀ O hy hcut hB h23 hFk hlot hpl hJ z q₀ hLP hK5
    (hgrp_link_at h 𝔇₀ Bs.G₀ (m + 1))

/-- **At the head's place.** -/
theorem hHands_head_paid
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true)
    {Fk : Nat → S → Prop}
    (hFk : ∀ s, Fk 339 s → ∃ z, Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ L.blocks Bs.G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {ft : Nat} (z : ProofFile.InstPub) {mk : ProofFile.LinksBy} (hG : ProofFile.blankBy mk Zp = some Bs.G₀)
    (hh : Bs.G₀.W.H.tl.heard = none)
    (hHP : headPlanB Zp (h.𝔇 𝔇₀).pubD.nsOf (h.𝔇 𝔇₀).pubD.d3 = true) :
    HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft 339 b' :=
  hHands_head_at h 𝔇₀ O hy hcut hB hFk hlot hpl z hG hh hHP (hgrp_link_at h 𝔇₀ Bs.G₀ 24)
    (htok_at h 𝔇₀ hlot hpl z)

/-- **At the finish.** -/
theorem hHands_fin_paid
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true)
    {Fk : Nat → S → Prop}
    (hFk : ∀ s, Fk 353 s → ∃ z, Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ L.blocks Bs.G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {ft : Nat} (z : ProofFile.InstPub) :
    HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft 353 b' :=
  hHands_fin_at h 𝔇₀ O hy hcut hB hFk hlot hpl z (hgrp_fin_at h 𝔇₀ Bs.G₀)

end Meaning.K2

#print axioms Meaning.K2.tok_of_left
#print axioms Meaning.K2.groupAt_const
#print axioms Meaning.K2.hgrp_link_at
#print axioms Meaning.K2.hgrp_fin_at
#print axioms Meaning.K2.htok_at
#print axioms Meaning.K2.hHands_link_paid
#print axioms Meaning.K2.hHands_head_paid
#print axioms Meaning.K2.hHands_fin_paid
