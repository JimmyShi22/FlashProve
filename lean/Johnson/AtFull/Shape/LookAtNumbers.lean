-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LookAtNumbers.lean: the lookups (the kind K3) at NUMBERED members of the first
chain, in the frame's own form: 49 of the fifty. Under the head `P5J.AtMgA`; general in the three
public files; a joining of two files: a site is made at each address (SitesAtHead.lean), and the
frames at a site (LookFrames.lean). Nothing is evaluated here.

Main names.
* `look_calls_no`: for l < 25: a site at link l on the calls; a member stands at number `lookNo l
  false`; and for every ft, g and vals with g ‹that number› = `liftQ (callsG s.shape s.p.first)`:
  `Carries`, and `Returns` under the two tests on public data.
* `look_digits_no`: for l < 24: the like at the digits, with the plan's two numbers u and c
  (`lookUC`).

Limits. `Returns` STILL KEEPS TWO TESTS WITH CODE ON PUBLIC DATA AS PREMISES (the face's own; at a
layers' calls: the site's shape is the layout's; at the digits: the plan's count behind). The second
test at the calls and the second at the digits keep disjuncts that are dead: the first of each
beside "s.digits = false" | "s.digits = true" in the same statement; at the digits the second too,
since a site below the head's link has not the head as its caller (see LookAtHead.lean's Limits).
The site's shape and first slot are under "there is". The head's own digits (member 345):
HeadDigitsFrame.lean. g and vals are letters: no table of steps is laid here. At the format's
second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SitesAtHead
import Johnson.AtFull.Shape.LookFrames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites usedAt callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (callsG digitsG)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The lookup on the calls, at all 25 links.** -/
theorem look_calls_no (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = false ∧
      (cF.blocksInOrder[lookNo l false]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo l false) = liftQ (callsG s.shape s.p.first) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo l false) ∧
          (s.at_.face.ok = true →
            (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true →
            Returns cF.blocksInOrder ft (firstZA g vals) (lookNo l false)) := by
  obtain ⟨s, hs, rfl, hd⟩ := site_made_at h l hl false
  obtain ⟨-, -, b, -, -, -, q, -, -⟩ := look_member_at h s hs
  rw [hd] at q
  exact ⟨s, hs, rfl, hd, by rw [q]; rfl,
    fun ft g vals hg => look_calls_frame h s hs hd ft g vals hg⟩

/-- **The lookup on the digits, at the 24 links that are not the head's.** -/
theorem look_digits_no (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 24) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      (cF.blocksInOrder[lookNo l true]?).isSome = true ∧
      ∃ u c, lookUC Zp.p.X l = some (u, c) ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo l true) = liftQ (digitsG s.shape s.p.first u c) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo l true) ∧
          (s.at_.face.ok = true →
            (!s.digits || s.caller == .head ||
              usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true →
            Returns cF.blocksInOrder ft (firstZA g vals) (lookNo l true)) := by
  obtain ⟨s, hs, rfl, hd⟩ := site_made_at h l (by omega) true
  obtain ⟨-, -, b, -, -, -, q, -, -⟩ := look_member_at h s hs
  rw [hd] at q
  have hc : s.caller ≠ .head := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
    rw [O.W] at k4 kN
    have hs' := hs
    unfold lookSites at hs'
    obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs'
    obtain ⟨-, -, f3, -, -, -, f7, -⟩ := site_facts _ _ y s hsy
    rw [← f3, k4, kN] at f7
    rw [f7]
    have e24 : s.link ≠ 24 := by omega
    by_cases he : s.link % 2 = 0 <;> simp [callerOf, e24, he]
  obtain ⟨u, c, hu, hF⟩ := look_digits_frame h s hs hd hc
  exact ⟨s, hs, rfl, hd, by rw [q]; rfl, u, c, hu, hF⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.look_calls_no
#print axioms Johnson.AtFull.Shape.look_digits_no
