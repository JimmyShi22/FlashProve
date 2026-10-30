-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SiteShape.lean: CONDITIONAL. AT THE LOOKUP ON THE CALLS OF A
LAYERS' LINK THE SITE's SHAPE IS THE LAYOUT's OWN: wherever the verifier's `publicOf` returns the
public part's record. THE FACT IS THE LIBRARY's; HERE IT IS LAID AT A SITE.

What is here. PUBLIC DATA ALONE: numbers of the plan. The authors of the kind "lookup" make, for
each lookup of a public part, a site (`Site`, `lookSites`: Honest/K3/Lot.lean); its field shape is
the shape that the place's own parameters fix (`P.shape`, Johnson/Desc/First/Look/LookKind.lean).
The layers' layout has a shape of its own, its field fo (OnBytes/Model/LayerLayout.lean). THE
LIBRARY HAS THAT THE TWO ARE ONE, AT THE PARAMETERS: `place_lay`
(Johnson/Desc/First/Look/K3PlaceLetters.lean): p.shape = some X.y.fo. What is here is its form at a
site: a few lines over `place_lay` and `site_facts` (Honest/K3/Law/MemberSite.lean). Statements with
their proofs; no definition.

  `site_shape_layers`: at a site; hh and hm are the two premises of `caller_layers`
      (Honest/K3/Law/MemberSite.lean). At every size: no hypothesis on the scope or on the hash.
  `site_shape_caller`: the same under hc : the site's caller is the layers. At every size.
  `site_shape_head`: under the library's hypothesis `P5J.AtMgA`, at link 2 g, g below 12. Its
      conclusion is spelled at `P5J.At.X` Zp, which is Zp.p.X by definition: a rewriting against the
      other spelling does not match; `exact` goes through. `P5J.AtMgA`'s field pubOne is spelled so
      too: whoever calls the first two at it may have to give (Z := Zp), as the proof here does.

Kin. `lookAt_lay`, `lay_shape` (Johnson/Desc/First/Look/K3CallerAtPlan.lean) lie beneath
`place_lay`; `place_att`, `place_head` (K3PlaceLetters.lean) have the like at an attention link and
at the model's last link. `callsShape_head` (Law/LookFitsFill.lean) goes the same way. OTHER WRITERS
HAVE A TWIN: `shape_layers_at` (Johnson/AtFull/Shape/LookFree.lean), to which the opening comment of
Honest/K3/LotPublic.lean points: by a letter of the kind's authors its statement is: under
`P5J.AtMgA`, hs, hd and hc : s.caller = .layers: s.shape = Zp.p.X.y.fo: that is `site_shape_caller`
under that hypothesis. That file stood outside the build over which this file was compiled, and was
not read for this pointer.

Not shown here. Nothing on the lookup on the digits. That a site stands at any link: hs is a premise
(`site_calls_head`, Honest/K3/Law/Thread/SiteThereHead.lean, has it under `P5J.AtMgA`). Neither the
named hypothesis `ShapeIsFs` nor its test with code `shapeIsFs` (Honest/K3/LotPublic.lean) is
concluded here; `heard_shape_layers` and `heard_shape_link` of the kind's authors take the test as a
premise. `site_shape_head`: THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH (`OnBytes.secondHashFunction`)
ALONE; it rests on a statement of a file under Johnson/Goal/, called by name: `Meaning.scope_plans`.
That h can hold: the side library AtFullSide proves, with no hypothesis, that h has a member at one
set of public files (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Nothing on soundness, on completeness or on any other property.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/ and under Johnson/Bridge/.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.First.Look.K3PlaceLetters
import Johnson.Road.K4.Riders.PlanOfScope
import Johnson.P5J.K03SlotsAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K3 (isHead)
open ProofFile.Honest.K3 (Site lookSites)

/-- CONDITIONAL: on all five hypotheses. **AT THE CALLS OF A LAYERS' LINK THE SITE's SHAPE IS THE
LAYOUT's OWN.** The library's `place_lay`, at a site. -/
theorem site_shape_layers {pol KL : ByteArray} {lay : Option ByteArray} {Z : ProofFile.Pub}
    (hX : Model.Verify.publicOf pol KL lay = .ok Z.p.X) {s : Site} (hs : s ∈ lookSites Z)
    (hd : s.digits = false) (hh : isHead Z.p.X s.link = false)
    (hm : (s.link % (if Z.p.X.p4 then 2 else 1) == 0) = true) : s.shape = Z.p.X.y.fo := by
  unfold lookSites at hs
  obtain ⟨x, -, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, -⟩ := ProofFile.Honest.K3.Law.site_facts _ _ x s hsx
  rw [← f3, ← f4, hd] at f1
  unfold isHead at hh
  obtain ⟨-, -, f5, -⟩ := VerifiableInference.Desc.First.Look.place_lay hX f1
    (beq_eq_false_iff_ne.1 hh) (eq_of_beq hm)
  exact Option.some.inj (f2.symm.trans f5)

/-- CONDITIONAL: on all four hypotheses. The same where the site's caller is the layers. -/
theorem site_shape_caller {pol KL : ByteArray} {lay : Option ByteArray} {Z : ProofFile.Pub}
    (hX : Model.Verify.publicOf pol KL lay = .ok Z.p.X) {s : Site} (hs : s ∈ lookSites Z)
    (hd : s.digits = false) (hc : s.caller = .layers) : s.shape = Z.p.X.y.fo := by
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, -, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨-, -, f3, -, -, -, f7, -⟩ := ProofFile.Honest.K3.Law.site_facts _ _ x s hsx
  rw [f7, ← f3] at hc
  by_cases hh : isHead Z.p.X s.link = true
  · rw [ProofFile.Honest.K3.Law.caller_head _ _ hh] at hc
    cases hc
  · have hh' : isHead Z.p.X s.link = false := Bool.eq_false_iff.2 hh
    by_cases hm : (s.link % (if Z.p.X.p4 then 2 else 1) == 0) = true
    · exact site_shape_layers hX hs hd hh' hm
    · rw [ProofFile.Honest.K3.Law.caller_attention _ _ hh' hm] at hc
      cases hc

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on all five hypotheses. **UNDER THE LIBRARY's HYPOTHESIS `P5J.AtMgA`, AT LINK
2 g.** -/
theorem site_shape_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {s : Site} (hs : s ∈ lookSites Zp) (hl : s.link = 2 * g) (hd : s.digits = false) :
    s.shape = (P5J.At.X Zp).y.fo := by
  obtain ⟨h4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have h4' : Zp.p.X.p4 = true := h4
  have hN' : Zp.p.X.NGr = 12 := hN
  refine site_shape_layers (Z := Zp) h.pubOne hs hd ?_ ?_
  · rw [hl]
    exact OnBytes.Road.K4.Riders.not_head h4' hN' hg
  · rw [hl, h4', if_pos rfl, Nat.mul_mod_right]
    rfl

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.site_shape_layers
#print axioms ProofFile.Honest.K4.W.site_shape_caller
#print axioms ProofFile.Honest.K4.W.site_shape_head
