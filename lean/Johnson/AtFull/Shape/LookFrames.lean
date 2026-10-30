-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LookFrames.lean: the lookups (the kind K3) at their sites, in the frame's own
form at the whole `ShA` (the chain's shape with the rows' makes:
Johnson/AtFull/Shape/FrameForm.lean); and the two numbers of the quiet step behind a lookup on the
digits, off the plan. Under the head `P5J.AtMgA`; a joining of laws; nothing is evaluated.

Main names.
* `calls_rest`, `digits_rest`: what the lookups' own sentences on what a lookup's member keeps
  (`K3KeepsCalls`, `K3KeepsDigits`: Johnson/Desc/ProofFile/Honest/K3/Law/Thread/K3Keeps.lean) give
  for the rows' makes: the statement stays.
* `lookUC X l`: the plan's two numbers at link l: at an even link the layers' plan's `used` and
  `nLin` of group l / 2; at an odd one the attention's plan's `nMsg` and `nLin`.
* `quiet_digits_at`: under the head, at a site of a link that is not the head's: `lookUC Zp.p.X
  s.link` returns two numbers, and the quiet step behind that link's lookup on the digits
  (`K3.quietAt … true`) is `quietDigits` at these. SO THE PREMISE hq OF `look_digits_at`
  (LookAtHead.lean) IS PAID.
* `look_calls_frame`: at a site on the calls: for every ft, g and vals with g ‹the member's number›
  = `liftQ (callsG s.shape s.p.first)`: `Carries` at `firstZA g vals`; and, under the two tests
  with code on public data of `look_calls_at`, `Returns`.
* `look_digits_frame`: at a site on the digits of a link that is not the head's: there are the two
  numbers u and c with `lookUC Zp.p.X s.link = some (u, c)` such that the same holds at `liftQ
  (digitsG s.shape s.p.first u c)`.
No test on values is asked: vals stays a free letter.

Limits. AT A SITE: THAT A SITE IS MADE AT EACH OF THE FIFTY ADDRESSES IS NOT SHOWN HERE: so no count
of members follows from this file alone. (SitesAtHead.lean's site_made_at says that a site of the
link and flag is made at each address.) The head's own digits have no step. The tests on public data
(the face's own; the site's shape is the layout's; the plan's count behind) are premises of
`Returns`, paid nowhere here. The second test at the calls and the second at the digits keep
disjuncts that are dead under the statements' own premises (see LookAtHead.lean's Limits). A table
that calls lookUC outside quiet_digits_at's premises has no law on what it gets. g and vals are
letters: no table of steps is laid here. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.LookAtHead
import Johnson.AtFull.Shape.RoundFrames
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName Place)
open VerifiableInference.Desc.K3 (quietAt quietDigits isHead)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites usedAt callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (callsG digitsG carriesR_calls carriesR_digits K3KeepsCalls
  K3KeepsDigits k3Keeps_calls k3Keeps_digits)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 What a lookup's member leaves of the statement -/

theorem calls_rest {h : Forest.Shape} {s s' : S} (K : K3KeepsCalls h s s') : s'.st = s.st := by
  obtain ⟨-, F, H, G, -, hC, -⟩ := K
  rcases hC with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨a, -, -, rfl⟩ <;> rfl

theorem digits_rest {h : Forest.Shape} {c : Nat} {s s' : S} (K : K3KeepsDigits h c s s') :
    s'.st = s.st := by
  obtain ⟨-, tl, F, H, G, -, -, hC, -⟩ := K
  rcases hC with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨a, -, -, rfl⟩ <;> rfl

/-! ## 2 The quiet step's two numbers, off the plan -/

/-- The plan's two numbers at link l. THE FULL SIZE's TEXT: it takes the step 2 where the library's
quietAt has "if X.p4 then 2 else 1", and does not part the head's link (at 24 it answers with
X.G[12]?): its one tie to quietAt is quiet_digits_at, under the head, at a caller that is not the
head. -/
def lookUC (X : Verify.Public) (l : Nat) : Option (Nat × Nat) :=
  if l % 2 == 0 then X.G[l / 2]?.map fun hp => (hp.used, hp.nLin)
  else X.A[l / 2]?.map fun a => (a.nMsg, a.nLin)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head, at a site of a link that is not the head's: lookUC returns two numbers, and the
quiet step behind that link's lookup on the digits is quietDigits at these. (No premise asks that s
itself be on the digits.) -/
theorem quiet_digits_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hc : s.caller ≠ .head) :
    ∃ u c, lookUC Zp.p.X s.link = some (u, c) ∧
      quietAt Zp.p.X s.link true = some (quietDigits u c) := by
  obtain ⟨hl, -, -⟩ := site_place_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨k4, kN, -, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  have hGA := Meaning.scope_plans24 h.scope h.reads O.public
  rw [O.W] at k4 kN hGA
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨-, -, f3, -, -, -, f7, -⟩ := site_facts _ _ y s hsy
  rw [← f3, k4, kN] at f7
  have h24 : s.link ≠ 24 := by
    intro e
    apply hc
    rw [f7, e]
    rfl
  have hH : isHead Zp.p.X s.link = false := by
    unfold isHead
    rw [k4, kN]
    simpa using h24
  unfold quietAt lookUC
  rw [hH, k4]
  by_cases he : s.link % 2 = 0
  · obtain ⟨⟨hp, e⟩, -⟩ := hGA (s.link / 2) (by omega)
    refine ⟨hp.used, hp.nLin, ?_, ?_⟩ <;> simp [he, e]
  · obtain ⟨-, a, e, -⟩ := hGA (s.link / 2) (by omega)
    refine ⟨a.nMsg, a.nLin, ?_, ?_⟩ <;> simp [he, e]

/-! ## 3 The frames -/

/-- **At a site on the calls, in the frame's form.** -/
theorem look_calls_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = false) (ft : Nat)
    (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (lookNo s.link false) = liftQ (callsG s.shape s.p.first)) :
    Carries cF.blocksInOrder ft (firstZA g vals) (lookNo s.link false) ∧
      (s.at_.face.ok = true →
        (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true →
        Returns cF.blocksInOrder ft (firstZA g vals) (lookNo s.link false)) := by
  obtain ⟨Bs', lot, b, hB, hin, hlp, q, hbp, hpk⟩ := look_member_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (hB.symm.trans O.made)
  rw [hd] at q
  refine ⟨fun blk hblk sj rs cols sj' n t hst hgt => ?_, fun hok hT2 blk hblk sj rs cols t hgt hF
    hv => ?_⟩
  · obtain rfl : b = blk := Option.some.inj (q.symm.trans hblk)
    have hgt' : g (lookNo s.link false) (shA sj) = .ok t := hgt
    rw [hg] at hgt'
    obtain ⟨v, hv⟩ := liftQ_ok hgt'
    have hm := List.mem_of_getElem? q
    obtain rfl : v = chainSh sj' := carriesR_calls _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot b hin hlp hm
      hbp hpk ft sj sj' n rs cols v hst hv
    have k1 := calls_rest (k3Keeps_calls _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot b hin hlp hm
      hbp hpk ft sj sj' n rs cols hst)
    rw [liftQ_at hv k1] at hgt'
    exact (Except.ok.inj hgt').symm
  · have hgt' : g (lookNo s.link false) (shA sj) = .ok t := hgt
    rw [hg] at hgt'
    obtain ⟨v, hv'⟩ := liftQ_ok hgt'
    exact (look_calls_at h s hs hd ft (fun _ => callsG s.shape s.p.first) vals rfl).2 hok hT2 blk
      hblk sj rs cols v hv' hF hv

/-- **At a site on the digits of a link that is not the head's, in the frame's form.** -/
theorem look_digits_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (hc : s.caller ≠ .head) :
    ∃ u c, lookUC Zp.p.X s.link = some (u, c) ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo s.link true) = liftQ (digitsG s.shape s.p.first u c) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo s.link true) ∧
          (s.at_.face.ok = true →
            (!s.digits || s.caller == .head ||
              usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true →
            Returns cF.blocksInOrder ft (firstZA g vals) (lookNo s.link true)) := by
  obtain ⟨u, c, hu, hq⟩ := quiet_digits_at h s hs hc
  obtain ⟨Bs', lot, b, hB, hin, hlp, q, hbp, hpk⟩ := look_member_at h s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (hB.symm.trans O.made)
  rw [hd] at q
  refine ⟨u, c, hu, fun ft g vals hg => ⟨fun blk hblk sj rs cols sj' n t hst hgt => ?_,
    fun hok hT3 blk hblk sj rs cols t hgt hF hv => ?_⟩⟩
  · obtain rfl : b = blk := Option.some.inj (q.symm.trans hblk)
    have hgt' : g (lookNo s.link true) (shA sj) = .ok t := hgt
    rw [hg] at hgt'
    obtain ⟨v, hv⟩ := liftQ_ok hgt'
    have hm := List.mem_of_getElem? q
    obtain rfl : v = chainSh sj' := carriesR_digits _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot b hin hlp
      hm hbp hpk u c hq ft sj sj' n rs cols v hst hv
    have k1 := digits_rest (k3Keeps_digits _ _ _ _ _ _ _ _ _ _ _ O s hs hd lot b hin hlp
      hm hbp hpk u c hq ft sj sj' n rs cols hst)
    rw [liftQ_at hv k1] at hgt'
    exact (Except.ok.inj hgt').symm
  · have hgt' : g (lookNo s.link true) (shA sj) = .ok t := hgt
    rw [hg] at hgt'
    obtain ⟨v, hv'⟩ := liftQ_ok hgt'
    exact (look_digits_at h s hs hd hc u c hq ft (fun _ => digitsG s.shape s.p.first u c) vals
      rfl).2 hok hT3 blk hblk sj rs cols v hv' hF hv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.calls_rest
#print axioms Johnson.AtFull.Shape.digits_rest
#print axioms Johnson.AtFull.Shape.quiet_digits_at
#print axioms Johnson.AtFull.Shape.look_calls_frame
#print axioms Johnson.AtFull.Shape.look_digits_frame
#print axioms Johnson.AtFull.Shape.lookUC
