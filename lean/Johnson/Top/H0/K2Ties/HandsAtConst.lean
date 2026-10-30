-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/HandsAtConst.lean: the code switch (K2): THE FIELD hHands OF ITS CONDITION AT
THE COMPOSED MEANING's CONSTANT (𝔇 := h.𝔇 𝔇₀, under the one head AtMg), AT EACH OF THE 25 PLACES, IN
THE FIELD's OWN LETTERS, WITH FIVE PAYERS CALLED. A join: nothing new is shown of
any sub-protocol. A file beneath the condition. A law file; no running text
imports it.

  const_lines     the three equations of HandsPlan.lean and «N is the constant's», at h.𝔇 𝔇₀: the
                  constant's own lines (Johnson/P5J/LettersRec.lean), by unfolding; the written row
                  of sorts by links_full.
  hHands_link_at  at 14 (m + 1) + 2, m < 23 · hHands_head_at at 339 · hHands_fin_at at 353: each
                  ends: HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
                    (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft ‹the place› b.
CALLED: HandsPlan.lean's three arms · d_link_laid, d_head_laid, d_finish_laid
(Johnson/P1K2R/DebtsLaid.lean: the debts on the numbers, at the constant's own N) · fresh_reached
(Johnson/Top/H0/Tw/K2C/HeadFreshReached.lean) · hU_reached
(Johnson/Top/H0/Tw/K2C/HeadUnheardReached.lean) · reach_raw (Johnson/Top/H0/Walk/Reach.lean).
WHAT STAYS IN FRONT, BY NAME:
  the head h : AtMg · the opening O at the head's own letters · hFk (under the fence the state is
  reached) · hlot hpl hJ (the sub-protocol is the lot's, at its place, joined);
  THREE NAMED TESTS THAT d_*_laid SPEND: hy (madePinnedAt) · hcut (the chain's blocks have the
  written cut) · hB (sendsAreB at 358);
  THREE NAMED TESTS ON THE PLANNER's OUTPUT: linkPlanB · k5PlanB (at attention's segments) ·
  headPlanB;
  hgrp (the plan's number of the group is the place's) at each arm: no payer was found by a search
  of the theorems' names in five sets of this project's Lean files;
  at the head: hG (the ground is the one made for a request of zeros) · hh (the head's plan has
  heard nothing) · htok (the public item «the token is small» rides over the step):
  tokSmall_reach and its kin (Johnson/IMR/TokAtReach.lean) lie near: NOT JOINED.
WHICH OF THE SIX TESTS A TEXT OF THE VERIFIER ASKS IS NOT SAID HERE (of the three on the planner's
output their own file says: none). NO MEMBER: that these premises can be met together is not shown.
Limits. The full size alone. At secondHashFunction alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Ties.HandsPlan
import Johnson.P1K2R.DebtsLaid
import Johnson.Top.H0.Tw.K2C.HeadUnheardReached
import Johnson.P5J.MgAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open VerifiableInference.Desc.Sound (below mgAll mgBase MgData)
open P1K2 (EP EQ prepOf numsAt linkPlanB k5PlanB headPlanB d_link_laid d_head_laid d_finish_laid)
open VerifiableInference.Desc.First.K2 (fresh_reached hU_reached)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open IM (HandsR Yes linksW placesW subW Joined)
open P5J (AtMg F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok OnBytes.Flat.numsFull.rows
    (P5J.colsAt OnBytes.Flat.numsFull) nR (P5J.At.X Zp))

/-- The constant's own lines. -/
theorem const_lines : (h.𝔇 𝔇₀).shape = Zp.first.shape ∧ (h.𝔇 𝔇₀).links = linksW ∧
    (h.𝔇 𝔇₀).built = Zp.p.built.links ∧ (h.𝔇 𝔇₀).N = P5J.At.N Zp cF :=
  ⟨rfl, links_full.symm, rfl, rfl⟩

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the 23 places that open a segment's link.** -/
theorem hHands_link_at
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
      k5PlanB Zp (h.𝔇 𝔇₀).pubD.d5 Zp.first.layout (m + 1) = true)
    (hgrp : ∀ P n, prepOf Zp Bs.G₀ = some P → numsAt P (some (m + 1)) = some n →
      (h.𝔇 𝔇₀).N.groupAt (m + 1) = n.grp) :
    HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft (14 * (m + 1) + 2) b :=
  hHands_link_B (h.𝔇 𝔇₀) h.scope h.reads O (by omega) (by omega) hFk hlot hpl hJ z q₀
    (const_lines h 𝔇₀).1 (const_lines h 𝔇₀).2.1 (const_lines h 𝔇₀).2.2.1 hLP hK5 hgrp
    (d_link_laid h.scope h.reads h.laid O hy hcut hB h23 hFk)

/-- **At the head's place.** -/
theorem hHands_head_at
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
    (hHP : headPlanB Zp (h.𝔇 𝔇₀).pubD.nsOf (h.𝔇 𝔇₀).pubD.d3 = true)
    (hgrp : ∀ P n, prepOf Zp Bs.G₀ = some P → numsAt P (some 24) = some n →
      (h.𝔇 𝔇₀).N.groupAt 24 = n.grp)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll (h.𝔇 𝔇₀).pubD noPub .tokenSmall (z, s) = true →
      pubAll (h.𝔇 𝔇₀).pubD noPub .tokenSmall (z, s') = true) :
    HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft 339 b' :=
  hHands_head_B (h.𝔇 𝔇₀) h.scope h.reads O hFk hlot hpl z
    (const_lines h 𝔇₀).1 (const_lines h 𝔇₀).2.1 (const_lines h 𝔇₀).2.2.1 hG hHP hgrp
    (fun s hf _ => by
      obtain ⟨z', hr⟩ := hFk s hf
      exact fresh_reached h.scope h.reads O s (reach_raw hr))
    (d_head_laid h.scope h.reads h.laid O hy hcut hB hFk) htok
    (fun s hf _ => by
      obtain ⟨z', hr⟩ := hFk s hf
      exact hU_reached h.scope h.reads O hh s (reach_raw hr))

/-- **At the finish.** -/
theorem hHands_fin_at
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true)
    {Fk : Nat → S → Prop}
    (hFk : ∀ s, Fk 353 s → ∃ z, Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ L.blocks Bs.G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {ft : Nat} (z : ProofFile.InstPub)
    (hgrp : ∀ P n, prepOf Zp Bs.G₀ = some P → numsAt P none = some n →
      (h.𝔇 𝔇₀).N.groupAt 25 = n.grp) :
    HandsR Fk (h.𝔇 𝔇₀).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (h.𝔇 𝔇₀) mgBase) P5J.fullLinks P5J.At.ps z) ft 353 b' :=
  hHands_fin_B (h.𝔇 𝔇₀) hlot hpl z hgrp (d_finish_laid h.scope h.reads h.laid O hy hcut hB hFk)

end Meaning.K2

#print axioms Meaning.K2.const_lines
#print axioms Meaning.K2.hHands_link_at
#print axioms Meaning.K2.hHands_head_at
#print axioms Meaning.K2.hHands_fin_at
