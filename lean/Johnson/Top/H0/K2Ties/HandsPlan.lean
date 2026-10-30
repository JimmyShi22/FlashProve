-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/HandsPlan.lean: the code switch (K2): THE FIELD hHands OF ITS CONDITION AT THE
CONSTANT's OWN LISTS (P5J.fullLinks · P5J.At.ps), AT EACH OF THE 25 PLACES, WITH WHAT FALLS BY THE
TEXT OF THE PUBLIC TESTS' PARAMETERS (MgData.pubD, Johnson/Desc/Sound/MgAll.lean) GONE, AND THE
SHARES' PREMISES ON THE PLANNER's OUTPUT AS THREE NAMED TESTS WITH CODE. General in the structure of
parameters 𝔇, under three equations that are the constant's own lines. A file beneath the
condition. A law file; no running text imports it.

  links_full · places_full   the written lists are the constant's (by linksW_full,
                  placesW_full: Johnson/Desc/AtSeats/HearAtFifty.lean).
  hands_at_full   HandsR at the shares' key and the written lists gives HandsR at the field's key
                  and the constant's lists.
  hdS_of          the shares' premise hdS at D₀ := 𝔇.pubD, from eS eL eB.
  hHands_link_B · hHands_head_B · hHands_fin_B   the three arms.
GONE, AGAINST HandsKey.lean's ARMS: hdS · hD5 · K5Plan's hOwn (by pubD's text, under eS : 𝔇.shape =
Z.first.shape · eL : 𝔇.links = linksW · eB : 𝔇.built = Z.p.built.links) · hFp (a theorem at the
ground that is made for a request of zeros: hFp_of_blank) · LinkPlan, K5Plan with hμc, HeadPlan:
each from ONE NAMED TEST's accept (linkPlanB · k5PlanB · headPlanB: Johnson/P1K2R/PlanBools.lean).
THE THREE TESTS ARE ASKED BY NO TEXT OF THE VERIFIER, AND ARE EVALUATED NOWHERE HERE.
WHAT STAYS BESIDE THEM: in scope · the files read · the opening · hFk · hlot hpl hJ · hgrp · the
debts on the numbers (Dd | D) · at the head: hG (the ground) · fresh · htok · hU.
THE LETTER q₀ OF THE FIRST ARM: any attention's plan. At a segment that is no attention's the
share's letter q is read by nothing, but Lean wants a value of the type, which has no default.
Limits. The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Ties.HandsKey
import Johnson.P1K2R.PlanBools
import Johnson.Desc.AtSeats.HearAtFifty
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc.Sound (below mgAll mgBase MgData)
open P1K2 (EP EQ prepOf numsAt linkPlanB k5PlanB headPlanB linkPlan_of_B k5Plan_of_B headPlan_of_B
  hFp_of_blank)
open VerifiableInference.Desc.First.K2 (LinkDebts SwitchDebts HeadFresh frontAt frameAt
  finishFrontQ)
open VerifiableInference.Desc.First.FillSent (sentDataAt)
open IM (HandsR XK Yes linksW placesW subW Joined k2P)
open _root_.Tw.K2 (firstFront switchNotices)

theorem links_full : linksW = P5J.fullLinks := HashBuild.linksW_full

theorem places_full : placesW = P5J.At.ps := HashBuild.placesW_full

variable {Xi Q Tok : Type} {rows cols nR : ℕ} {X₀ : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi Q Tok rows cols nR X₀)

theorem hands_at_full (z : Q) {Fk : Nat → S → Prop} {N : Numbers} {ft k : Nat} {b : Block S Cl}
    (H : HandsR Fk N linksW placesW (EP 𝔇.pubD noPub z) ft k b) :
    HandsR Fk N P5J.fullLinks P5J.At.ps (EQ (mgAll 𝔇 mgBase) P5J.fullLinks P5J.At.ps z) ft k b := by
  have h := hands_at_key 𝔇 z H
  rw [places_full, links_full] at h
  exact h

theorem hdS_of {Z : ProofFile.Pub} (eS : 𝔇.shape = Z.first.shape) (eL : 𝔇.links = linksW)
    (eB : 𝔇.built = Z.p.built.links) :
    𝔇.pubD.dS = sentDataAt Z.first.shape 𝔇.N linksW placesW Z.p.built.links := by
  show sentDataAt 𝔇.shape 𝔇.N 𝔇.links (flatPlacesOf 𝔇.links true) 𝔇.built = _
  rw [eS, eL, eB]
  rfl

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At the 23 places that open a segment's link.** -/
theorem hHands_link_B (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : Nat → S → Prop}
    {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    (hFk : ∀ s, Fk (14 * l + 2) s →
      ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s))
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {ft : Nat} (z : Q) (q₀ : Attention.Plan) (eS : 𝔇.shape = Z.first.shape)
    (eL : 𝔇.links = linksW) (eB : 𝔇.built = Z.p.built.links)
    (hLP : linkPlanB Z 𝔇.pubD.nsOf 𝔇.pubD.d3 l = true)
    (hK5 : subW l = .attention → k5PlanB Z 𝔇.pubD.d5 Z.first.layout l = true)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → 𝔇.N.groupAt l = n.grp)
    (Dd : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK 𝔇.N linksW placesW (EP 𝔇.pubD noPub z) (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts 𝔇.N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay) :
    HandsR Fk 𝔇.N P5J.fullLinks P5J.At.ps (EQ (mgAll 𝔇 mgBase) P5J.fullLinks P5J.At.ps z) ft
      (14 * l + 2) b := by
  have hD5 : 𝔇.pubD.d5.shape = Z.first.shape := eS
  by_cases ha : subW l = .attention
  · obtain ⟨q, μ, P5, hμ⟩ := k5Plan_of_B (D := 𝔇.pubD) (N := 𝔇.N) (hK5 ha) rfl
    rw [hD5] at hμ
    exact hands_at_full 𝔇 z (share_firstX hS hR O h1 h24 hFk hlot hpl hJ 𝔇.pubD noPub z
      (linkPlan_of_B hLP) (fun _ => P5) hD5 (fun _ => hμ) hgrp Dd (hdS_of 𝔇 eS eL eB))
  · exact hands_at_full 𝔇 z (share_firstX (q := q₀) (μ := 0) hS hR O h1 h24 hFk hlot hpl hJ
      𝔇.pubD noPub z (linkPlan_of_B hLP) (fun h => absurd h ha) hD5 (fun h => absurd h ha) hgrp Dd
      (hdS_of 𝔇 eS eL eB))

/-- **At the head's place.** -/
theorem hHands_head_B (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : Nat → S → Prop}
    {G₀ : ProofFile.Ground}
    (hFk : ∀ s, Fk 339 s → ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {ft : Nat} (z : Q) (eS : 𝔇.shape = Z.first.shape) (eL : 𝔇.links = linksW)
    (eB : 𝔇.built = Z.p.built.links) {mk : ProofFile.LinksBy} (hG : ProofFile.blankBy mk Z = some G₀)
    (hHP : headPlanB Z 𝔇.pubD.nsOf 𝔇.pubD.d3 = true)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → 𝔇.N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK 𝔇.N linksW placesW (EP 𝔇.pubD noPub z) 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK 𝔇.N linksW placesW (EP 𝔇.pubD noPub z) 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts 𝔇.N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll 𝔇.pubD noPub .tokenSmall (z, s) = true →
      pubAll 𝔇.pubD noPub .tokenSmall (z, s') = true)
    (hU : ∀ s, Fk 339 s → XK 𝔇.N linksW placesW (EP 𝔇.pubD noPub z) 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none) :
    HandsR Fk 𝔇.N P5J.fullLinks P5J.At.ps (EQ (mgAll 𝔇 mgBase) P5J.fullLinks P5J.At.ps z) ft 339
      b' :=
  hands_at_full 𝔇 z (share_hearX hS hR O hFk hlot hpl 𝔇.pubD noPub z (headPlan_of_B hG hHP) hgrp
    fresh D htok hU (hdS_of 𝔇 eS eL eB) (hFp_of_blank hG))

/-- **At the finish.** -/
theorem hHands_fin_B {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    {ft : Nat} (z : Q)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n → 𝔇.N.groupAt 25 = n.grp)
    (D : ∀ nm P n (s t : S) x W lay, prepOf Z G₀ = some P → numsAt P none = some n →
      Fk 353 s → XK 𝔇.N linksW placesW (EP 𝔇.pubD noPub z) 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts 𝔇.N 25 placesW[353]? placesW[353 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size) x W lay) :
    HandsR Fk 𝔇.N P5J.fullLinks P5J.At.ps (EQ (mgAll 𝔇 mgBase) P5J.fullLinks P5J.At.ps z) ft 353
      b' :=
  hands_at_full 𝔇 z (P1K2.share_backP hlot hpl 𝔇.pubD noPub z hgrp D)

end Meaning.K2

#print axioms Meaning.K2.links_full
#print axioms Meaning.K2.places_full
#print axioms Meaning.K2.hands_at_full
#print axioms Meaning.K2.hdS_of
#print axioms Meaning.K2.hHands_link_B
#print axioms Meaning.K2.hHands_head_B
#print axioms Meaning.K2.hHands_fin_B
