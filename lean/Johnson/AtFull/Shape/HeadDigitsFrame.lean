-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/HeadDigitsFrame.lean: THE FIFTIETH LOOKUP: the one on the digits of the head's
link (member 345 of the first chain), in the frame's own form: `Carries` and `Returns`
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) at the letters `firstZA g vals`
(Johnson/AtFull/Shape/FrameForm.lean). Under the head `P5J.AtMgA`; general in the three public
files; a joining of laws; nothing is evaluated.

The step on the chain's shape, `headDigitsG`, and its two laws are the lookups' own
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CarriesHeadDigits.lean). What these take as premises on
the description's return, the site, the lot's sub-protocol, the member and what stands behind the
lookup is paid here.

Main names.
* `quiet_head_at`: under the head, behind the lookup on the digits of link 24 stands the library's
  `quietHead`.
* `head_caller_at`: a site at link 24 has the head as its caller.
* `look_head_frame`: at EVERY site s in `lookSites Zp` at link 24 on the digits: a member stands at
  345; and for every ft, g and vals with g 345 = `liftQ (headDigitsG s.shape s.p.first Zp.p.X)`:
  `Carries` at 345 under hL; `Returns` at 345 under hok, hN and hv.
* `look_head_no`: there is such a site (`site_made_at`), with the same.

WHAT STAYS, BY NAME. hL: `layoutOk`: a test with code on public data (ClaimSizes.lean). hok: the
face's own test. hN: the head's plan counts one claim on the weights. hv: THE LETTER vals AT 345
GIVES `headVals` (ClaimReturns.lean): A TEST ON WHAT THE HEAD HEARD, NOT ON ITS SHAPE: the library's
`weightsClaim` refuses at values, and no guard on the shape can decide it: whoever lays vals lays it
so.

Limits. FOUR PREMISES STAY; NONE IS SHOWN OR EVALUATED HERE. The lookups' own word on their step:
the youngest and the least tried of the fifty. The site's shape and first slot are under "there is".
g and vals are letters: no table of steps is laid here. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SitesAtHead
import Johnson.AtFull.Shape.LookFrames
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesHeadDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName Place)
open VerifiableInference.Desc.K3 (isHead quietAt quietHead)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (headDigitsG carriesR_headDigits returns_headDigits
  headDigits_stateW layoutOk headVals)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head, behind the lookup on the digits of link 24 stands `quietHead`. -/
theorem quiet_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    quietAt Zp.p.X 24 true = some (quietHead Zp.p.X) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  rw [O.W] at k4 kN
  have hH : isHead Zp.p.X 24 = true := by
    unfold isHead
    rw [k4, kN]
    rfl
  unfold quietAt
  rw [hH]
  rfl

/-- A site at link 24 has the head as its caller. -/
theorem head_caller_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link = 24) : s.caller = .head := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  rw [O.W] at k4 kN
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨-, -, f3, -, -, -, f7, -⟩ := site_facts _ _ y s hsy
  rw [← f3, k4, kN, hl] at f7
  rw [f7]
  rfl

/-- **THE FIFTIETH LOOKUP, IN THE FRAME's FORM, AT EVERY SITE OF LINK 24 ON THE DIGITS.** -/
theorem look_head_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link = 24) (hd : s.digits = true) :
    (cF.blocksInOrder[345]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g 345 = liftQ (headDigitsG s.shape s.p.first Zp.p.X) →
        (layoutOk Zp.p.X.HLy Zp.p.X.layers.wsLay = true →
          Carries cF.blocksInOrder ft (firstZA g vals) 345) ∧
        (s.at_.face.ok = true → (Zp.p.X.H.NCL == 1) = true →
          (∀ st rs cols, vals 345 st rs cols = true → headVals Zp.p.X st = true) →
          Returns cF.blocksInOrder ft (firstZA g vals) 345) := by
  obtain ⟨Bs', lot, b, hB, hin, hlp, q, hbp, hpk⟩ := look_member_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (hB.symm.trans O.made)
  rw [hl, hd] at q
  have q' : cF.blocksInOrder[345]? = some b := q
  have hq : quietAt Zp.p.X s.link true = some (quietHead Zp.p.X) := by
    rw [hl]
    exact quiet_head_at h
  have hc := head_caller_at h s hs hl
  have hm := List.mem_of_getElem? q'
  refine ⟨by rw [q']; rfl, fun ft g vals hg =>
    ⟨fun hL blk hblk sj rs cols sj' n t hst hgt => ?_,
      fun hok hN hv blk hblk sj rs cols t hgt hF hvv => ?_⟩⟩
  · obtain rfl : b = blk := Option.some.inj (q'.symm.trans hblk)
    have hgt' : g 345 (shA sj) = .ok t := hgt
    rw [hg] at hgt'
    obtain ⟨v, hv⟩ := liftQ_ok hgt'
    obtain rfl : v = chainSh sj' := carriesR_headDigits _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot b hin
      hlp hm hbp hpk hq hL ft sj sj' n rs cols v hst hv
    have k1 : sj'.st = sj.st := by
      obtain ⟨tl, F, H, G, a₀, cov, xx, tt, claim, -, -, -, -, -, -, -, -, e, -⟩ :=
        headDigits_stateW _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot b hin hlp hm hbp hpk hq ft sj sj' n
          rs cols hst
      rw [e]
    rw [liftQ_at hv k1] at hgt'
    exact (Except.ok.inj hgt').symm
  · have hgt' : g 345 (shA sj) = .ok t := hgt
    rw [hg] at hgt'
    obtain ⟨v, hv'⟩ := liftQ_ok hgt'
    exact returns_headDigits _ _ _ _ _ _ _ _ _ _ _ O s hs hd hc lot hin hlp hok hN cF.blocksInOrder ft 345
      (fun blk' hb' => by
        obtain rfl : b = blk' := Option.some.inj (q'.symm.trans hb')
        exact ⟨hm, hbp, hpk⟩)
      (fun _ => headDigitsG s.shape s.p.first Zp.p.X) vals rfl hv blk hblk sj rs cols v hv' hF hvv

/-- **At member 345, by number**: there is such a site (tied by its membership in lookSites, its
link 24 and its flag), a member stands at 345, and the frame's two premises hold there under the
premises that stay. -/
theorem look_head_no (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ s ∈ lookSites Zp, s.link = 24 ∧ s.digits = true ∧ (cF.blocksInOrder[345]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g 345 = liftQ (headDigitsG s.shape s.p.first Zp.p.X) →
        (layoutOk Zp.p.X.HLy Zp.p.X.layers.wsLay = true →
          Carries cF.blocksInOrder ft (firstZA g vals) 345) ∧
        (s.at_.face.ok = true → (Zp.p.X.H.NCL == 1) = true →
          (∀ st rs cols, vals 345 st rs cols = true → headVals Zp.p.X st = true) →
          Returns cF.blocksInOrder ft (firstZA g vals) 345) := by
  obtain ⟨s, hs, hl, hd⟩ := site_made_at h 24 (by omega) true
  obtain ⟨k, F⟩ := look_head_frame h s hs hl hd
  exact ⟨s, hs, hl, hd, k, F⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.quiet_head_at
#print axioms Johnson.AtFull.Shape.head_caller_at
#print axioms Johnson.AtFull.Shape.look_head_frame
#print axioms Johnson.AtFull.Shape.look_head_no
