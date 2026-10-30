-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LookFree.lean: THE 25 LOOKUPS ON THE CALLS, IN THE FRAME's OWN FORM, WITH NO
PREMISE LEFT BUT THE HEAD: `Carries` AND `Returns` (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean)
at the letters `firstZA g vals`, under the head `P5J.AtMgA`. GENERAL IN THE THREE PUBLIC FILES (in
the goals' scope); a joining of laws; nothing is evaluated.

What was left. The frames at a site on the calls (LookFrames.lean) take two public tests as premises
of `Returns`: the face's own test, and, at a layers' link, that seven numbers of the site's shape
are the layout's. The first is FaceAtSites.lean's, at every site. The second:
* `shape_layers_at`: at a site on the calls of a layers' link THE SITE's SHAPE IS THE LAYOUT's OWN
  RECORD OF IT, `Zp.p.X.y.fo`, whole: the layout's record is made of the layout's calls by the
  verifier program's own routine (`Fo.layout_shape`, OnBytes/Tie/Pv/Lookup/Ends/FoPublicShape.lean),
  the site's by `shapeOwn`, which agrees with that routine (`shapeOwn_eq`,
  Johnson/Desc/First/Look/ShapeOwnAgrees2.lean), of the same calls, cap and padding counts
  (`lookAt`'s text).

Main names.
* `sameShape_self`: the test on seven numbers accepts a shape against itself.
* `shape_layers_at`: as above.
* `look_calls_frame_free`: at EVERY site s in `lookSites Zp` on the calls: for every ft, g and vals
  with g ‹the member's number› = `liftQ (callsG s.shape s.p.first)`: both.
* `look_calls_free`: for l < 25: there is such a site at link l; a member stands at number `lookNo l
  false`; both.
* `look_digits_frame_face`, `look_head_frame_face`: the frames at the digits with the face's test
  paid: at a link that is not the head's `Returns` keeps the test on the slots in use alone; at the
  head's `Returns` keeps hN and hv, and `Carries` still stands under hL (`layoutOk`).

Limits. The site's shape and first slot are a letter's or under "there is". g and vals are letters:
no table of steps is laid here. `Carries` and `Returns` are two premises that the rule for
acceptance (`accepted_of_shape`, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) asks at each
member: here they stand at 25 of the chain's 358 members. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LookAtNumbers
import Johnson.AtFull.Shape.HeadDigitsFrame
import Johnson.AtFull.Shape.FaceAtSites
import Johnson.Goal.Meaning.OkScope
import Johnson.Desc.First.Look.ShapeOwnAgrees2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (sameShape placeAt lookAt shapeOwn pubOk shapeOwn_eq)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites usedAt callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (callsG digitsG headDigitsG layoutOk headVals)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The test on seven numbers accepts a shape against itself. -/
theorem sameShape_self (a : Forest.Shape) : sameShape a a = true := by
  simp [sameShape]

/-- **AT A SITE ON THE CALLS OF A LAYERS' LINK THE SITE's SHAPE IS THE LAYOUT's OWN RECORD.** -/
theorem shape_layers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = false) (hc : s.caller = .layers) :
    s.shape = Zp.p.X.y.fo := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads hX
  obtain ⟨h0, e1, -, e3⟩ := Fo.layout_shape (Meaning.P34.layout_of_public hX)
  rw [O.W] at k4 kN e1 e3
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, f2, f3, f4, -, -, f7, -⟩ := site_facts _ _ y s hsy
  rw [← f3, ← f4, hd] at f1
  rw [← f3, k4, kN, hc] at f7
  -- the link is even and not the head's
  have h24 : (s.link == 2 * 12) = false := by
    cases e : s.link == 2 * 12 with
    | false => rfl
    | true => simp [callerOf, e] at f7
  have hev : (s.link % 2 == 0) = true := by
    cases e : s.link % 2 == 0 with
    | true => rfl
    | false => simp [callerOf, h24, e] at f7
  -- the place
  unfold placeAt at f1
  obtain ⟨xx, hx, hp⟩ := Option.map_eq_some_iff.1 f1
  unfold lookAt at hx
  simp only [k4, kN, if_true, h24, hev, Bool.false_eq_true, if_false] at hx
  obtain ⟨hp2, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain rfl := Option.some.inj hx
  -- the shape
  have f2' : ((shapeOwn Zp.p.X.y.cl Zp.p.X.y.h.lidb).bind fun a =>
      if pubOk a Zp.p.X.y.fo.pub then some { a with pub := Zp.p.X.y.fo.pub } else none) =
        some s.shape := by
    rw [← f2, ← hp]
    rfl
  rw [shapeOwn_eq, e1] at f2'
  have f2'' : (if pubOk h0 Zp.p.X.y.fo.pub then
      some ({ h0 with pub := Zp.p.X.y.fo.pub } : Forest.Shape) else none) = some s.shape := f2'
  by_cases hpk : pubOk h0 Zp.p.X.y.fo.pub = true
  · rw [if_pos hpk] at f2''
    rw [← Option.some.inj f2'', ← e3]
  · rw [if_neg hpk] at f2''
    cases f2''

/-- **AT EVERY SITE ON THE CALLS: BOTH, WITH NO PREMISE BUT THE HEAD.** -/
theorem look_calls_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = false) (ft : Nat)
    (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (lookNo s.link false) = liftQ (callsG s.shape s.p.first)) :
    Carries cF.blocksInOrder ft (firstZA g vals) (lookNo s.link false) ∧
      Returns cF.blocksInOrder ft (firstZA g vals) (lookNo s.link false) := by
  obtain ⟨a, b⟩ := look_calls_frame h s hs hd ft g vals hg
  refine ⟨a, b (face_ok_site Zp s hs) ?_⟩
  by_cases hc : s.caller = .layers
  · rw [shape_layers_at h s hs hd hc, sameShape_self]
    simp
  · have : (s.caller != .layers) = true := by
      cases e : s.caller <;> simp_all
    rw [this]
    simp

/-- **AT THE 25 NUMBERED MEMBERS.** -/
theorem look_calls_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = false ∧
      (cF.blocksInOrder[lookNo l false]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo l false) = liftQ (callsG s.shape s.p.first) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo l false) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (lookNo l false) := by
  obtain ⟨s, hs, rfl, hd, k, -⟩ := look_calls_no h l hl
  exact ⟨s, hs, rfl, hd, k, fun ft g vals hg => look_calls_frame_free h s hs hd ft g vals hg⟩

/-- At the digits of a link that is not the head's, with the face's test paid. -/
theorem look_digits_frame_face (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (hc : s.caller ≠ .head) :
    ∃ u c, lookUC Zp.p.X s.link = some (u, c) ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo s.link true) = liftQ (digitsG s.shape s.p.first u c) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo s.link true) ∧
          ((!s.digits || s.caller == .head ||
              usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true →
            Returns cF.blocksInOrder ft (firstZA g vals) (lookNo s.link true)) := by
  obtain ⟨u, c, hu, F⟩ := look_digits_frame h s hs hd hc
  exact ⟨u, c, hu, fun ft g vals hg =>
    ⟨(F ft g vals hg).1, (F ft g vals hg).2 (face_ok_site Zp s hs)⟩⟩

/-- At the digits of the head's link, with the face's test paid. -/
theorem look_head_frame_face (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link = 24) (hd : s.digits = true) :
    (cF.blocksInOrder[345]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g 345 = liftQ (headDigitsG s.shape s.p.first Zp.p.X) →
        (layoutOk Zp.p.X.HLy Zp.p.X.layers.wsLay = true →
          Carries cF.blocksInOrder ft (firstZA g vals) 345) ∧
        ((Zp.p.X.H.NCL == 1) = true →
          (∀ st rs cols, vals 345 st rs cols = true → headVals Zp.p.X st = true) →
          Returns cF.blocksInOrder ft (firstZA g vals) 345) := by
  obtain ⟨k, F⟩ := look_head_frame h s hs hl hd
  exact ⟨k, fun ft g vals hg =>
    ⟨(F ft g vals hg).1, (F ft g vals hg).2 (face_ok_site Zp s hs)⟩⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sameShape_self
#print axioms Johnson.AtFull.Shape.shape_layers_at
#print axioms Johnson.AtFull.Shape.look_calls_frame_free
#print axioms Johnson.AtFull.Shape.look_calls_free
#print axioms Johnson.AtFull.Shape.look_digits_frame_face
#print axioms Johnson.AtFull.Shape.look_head_frame_face
