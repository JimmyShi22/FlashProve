-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/DigitsFree.lean: THE 24 LOOKUPS ON THE DIGITS OF THE LINKS THAT ARE NOT THE
HEAD's, IN THE FRAME's OWN FORM, WITH NO PREMISE LEFT BUT THE HEAD: `Carries` AND `Returns`
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) at the letters `firstZA g vals`, under the head
`P5J.AtMgA`. GENERAL IN THE THREE PUBLIC FILES (in the goals' scope); a joining of laws; nothing is
evaluated.

What was left (LookFree.lean: `look_digits_frame_face`): one public test: the plan's number of slots
in use is the lookup's first slot plus the face's hidden values. Why it holds.
* The plan's makers lay one number, msg, both as the link's number of slots and as the slots in use:
  `planG_used`, `planA_nMsg`: by the makers' own texts (Layer.planG, Attention.plan).
* The lookup's first slot is the link's number of slots less the scalars of the plan's record f9 of
  the lookup's shape (`lookAt`'s text; `digitsNext` returns only where that does not fall below 0).
* The site's shape IS that record: `Fo.ZPlan.public_shapeZ`
  (OnBytes/Tie/Pv/Lookup/Ends/FoShapeZ.lean) and `shape_of_made`
  (Johnson/Desc/First/Look/K3CallerCellsLaw.lean).
* The face counts as many hidden values as the program's model counts scalars: `slots_elems`
  (Honest/K3/Law/SlotsElems.lean).

Main names.
* `planG_used`, `planA_nMsg`: as above. General laws on the two makers.
* `used_at`: at every site s in `lookSites Zp` on the digits with s.link < 24: the test on the slots
  in use accepts, in the very form in which `returns_digits` takes it.
* `caller_below`: a site at a link below 24 has not the head as its caller. (LookAtNumbers.lean
  shows the same fact inline, in look_digits_no's proof.)
* `look_digits_frame_free`: at every such site: the plan's two numbers u and c (`lookUC`), and for
  every ft, g and vals with g ‹the member's number› = `liftQ (digitsG s.shape s.p.first u c)`: both.
* `look_digits_free`: for l < 24: there is such a site; a member stands at number `lookNo l true`;
  both.

Limits. The site's shape and first slot are a letter's or under "there is". used_at's test keeps two
disjuncts that are dead under its own premises (see LookAtHead.lean's Limits). g and vals are
letters: no table of steps is laid here. `Carries` and `Returns` are two premises that the rule for
acceptance (`accepted_of_shape`, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) asks at each
member: here they stand at 24 of the chain's 358 members. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LookFree
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems
import Johnson.Desc.ProofFile.Honest.K3.LotPublic
import Johnson.Desc.First.Look.K3CallerCellsLaw
import Johnson.Road.HeadDict
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open Fo.BatRows (bindE_ok)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt lookAt digitsNext shape_of_made)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites usedAt callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.Spec (slots_elems)
open ProofFile.Honest.K3.Law.AtThr (digitsG)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 The makers lay one number twice -/

/-- A layers' plan: the slots in use are the link's number of slots. -/
theorem planG_used (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.used = hp.ns := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    rfl
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      rfl
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

open Attention in
/-- An attention's plan: the slots that the messages take are the link's number of slots. -/
theorem planA_nMsg (settings : Settings) (i : In) (cf : Cfg) (P : Plan)
    (e : plan settings i cf = .ok P) : P.nMsg = P.ns := by
  unfold plan at e
  dsimp only at e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, h0, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, h1, e⟩ := bindE_ok e
  cases e
  rfl

/-! ## 2 The test on the slots in use -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE TEST ON THE SLOTS IN USE ACCEPTS AT EVERY SITE ON THE DIGITS OF A LINK BELOW 24.** -/
theorem used_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = true) (hl : s.link < 24) :
    (!s.digits || s.caller == .head ||
      usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  obtain ⟨k4, kN, -⟩ := Meaning.scope_plans h.scope h.reads hX
  obtain ⟨zG, zA, -⟩ := Fo.ZPlan.public_shapeZ hX
  obtain ⟨_, _, _, _, _, _, -, hPl⟩ := OnBytes.Road.Hd.public_plans hX
  have hAp := Fo.Pub.public_A hX
  rw [O.W] at k4 kN zG zA hPl hAp
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, f2, f3, f4, -, f6, f7, f8⟩ := site_facts _ _ y s hsy
  rw [← f3, ← f4, hd] at f1
  rw [← f3, k4, kN] at f7 f8
  have h24 : (s.link == 2 * 12) = false := beq_false_of_ne (by omega)
  unfold placeAt at f1
  obtain ⟨xx, hx, hp⟩ := Option.map_eq_some_iff.1 f1
  unfold lookAt at hx
  simp only [k4, kN, if_true, h24, Bool.false_eq_true, if_false] at hx
  have e24 : s.link ≠ 24 := by omega
  by_cases he : s.link % 2 = 0
  · -- a layers' link
    have hev : (s.link % 2 == 0) = true := by rw [he]; rfl
    simp only [hev, if_true] at hx
    obtain ⟨pl, hG, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨nx, hnx, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hsh : s.shape = pl.tl.f9 := by
      have := shape_of_made (p := s.p) (fs := pl.tl.f9) (by rw [← hp]; exact zG _ pl hG)
      rw [f2] at this
      exact Option.some.inj this
    have hfirst : s.p.first = nx := by rw [← hp]; rfl
    have hu : usedAt Zp.p.X s = some pl.ns := by
      unfold usedAt
      rw [f7, f8]
      simp only [callerOf, if_true, h24, hev, Bool.false_eq_true, if_false]
      rw [hG, Option.map_some, planG_used _ _ _ _ (Fo.Pub.plansG_at _ _ hPl _ pl hG)]
    unfold digitsNext at hnx
    split at hnx
    · rename_i hle
      obtain rfl := Option.some.inj hnx
      rw [hu, hfirst, f6, hsh, slots_elems]
      have : pl.ns - 0 - Forest.elems pl.tl.f9 + Forest.elems pl.tl.f9 = pl.ns := by omega
      rw [this]
      simp
    · cases hnx
  · -- an attention's link
    have hev : (s.link % 2 == 0) = false := beq_false_of_ne he
    simp only [hev, Bool.false_eq_true, if_false] at hx
    obtain ⟨a, hA, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨nx, hnx, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hsh : s.shape = a.seam.tl.f9 := by
      have := shape_of_made (p := s.p) (fs := a.seam.tl.f9) (by rw [← hp]; exact zA _ a hA)
      rw [f2] at this
      exact Option.some.inj this
    have hfirst : s.p.first = nx := by rw [← hp]; rfl
    have hn : a.nMsg = a.ns := by
      obtain ⟨_, _, _, a0, -, -, -, hpa, ea, -⟩ := hAp _ a hA
      rw [ea]
      exact planA_nMsg _ _ _ a0 hpa
    have hu : usedAt Zp.p.X s = some a.ns := by
      unfold usedAt
      rw [f7, f8]
      simp only [callerOf, if_true, h24, hev, Bool.false_eq_true, if_false]
      rw [hA, Option.map_some, hn]
    unfold digitsNext at hnx
    split at hnx
    · rename_i hle
      obtain rfl := Option.some.inj hnx
      rw [hu, hfirst, f6, hsh, slots_elems]
      have : a.ns - 0 - Forest.elems a.seam.tl.f9 + Forest.elems a.seam.tl.f9 = a.ns := by omega
      rw [this]
      simp
    · cases hnx

/-! ## 3 The frames -/

/-- A site at a link below 24 has not the head as its caller. -/
theorem caller_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 24) : s.caller ≠ .head := by
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

/-- **AT EVERY SITE ON THE DIGITS OF A LINK BELOW 24: BOTH, WITH NO PREMISE BUT THE HEAD.** -/
theorem look_digits_frame_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (hl : s.link < 24) :
    ∃ u c, lookUC Zp.p.X s.link = some (u, c) ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo s.link true) = liftQ (digitsG s.shape s.p.first u c) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo s.link true) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (lookNo s.link true) := by
  obtain ⟨u, c, hu, F⟩ := look_digits_frame_face h s hs hd (caller_below h s hs hl)
  exact ⟨u, c, hu, fun ft g vals hg =>
    ⟨(F ft g vals hg).1, (F ft g vals hg).2 (used_at h s hs hd hl)⟩⟩

/-- **AT THE 24 NUMBERED MEMBERS.** -/
theorem look_digits_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 24) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      (cF.blocksInOrder[lookNo l true]?).isSome = true ∧
      ∃ u c, lookUC Zp.p.X l = some (u, c) ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g (lookNo l true) = liftQ (digitsG s.shape s.p.first u c) →
        Carries cF.blocksInOrder ft (firstZA g vals) (lookNo l true) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (lookNo l true) := by
  obtain ⟨s, hs, e1, hd, k, u, c, hu, F⟩ := look_digits_no h l hl
  have hl' : s.link < 24 := by rw [e1]; exact hl
  exact ⟨s, hs, e1, hd, k, u, c, hu, fun ft g vals hg =>
    ⟨(F ft g vals hg).1, (F ft g vals hg).2 (face_ok_site Zp s hs) (used_at h s hs hd hl')⟩⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.planG_used
#print axioms Johnson.AtFull.Shape.planA_nMsg
#print axioms Johnson.AtFull.Shape.used_at
#print axioms Johnson.AtFull.Shape.caller_below
#print axioms Johnson.AtFull.Shape.look_digits_frame_free
#print axioms Johnson.AtFull.Shape.look_digits_free
