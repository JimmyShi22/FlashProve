-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ShapeIsFsPaid.lean: the kind "lookup" (K3): the named
public hypothesis `ShapeIsFs` (Honest/K3/LotPublic.lean: the site's shape is the shape that the plan
itself holds for it) holds at every site of a public part whose record the verifier's own
`Verify.publicOf` returns: on the calls of a layers', an attention and the head's link, and on the
digits of every link. So does its test with code, `shapeIsFs`. Theorems; no definition.

Why. Many theorems of this library take `ShapeIsFs Z.p.X s`, or `shapeIsFs Z.p.X s = true`, as a
hypothesis. The library has the sentence that pays it, in four laws on `P.ofPlace … x`, one for each
sort of place; here they are joined and carried to a site.

What is shown.
  `place_shape_fs`: conditional on hX: at every link, on the calls and on the digits: the shape that
    the place's parameters fix is the place's own field `fs`. A join of the library's `head_shape`,
    `lay_shape`, `att_shape` (Johnson/Desc/First/Look/K3CallerAtPlan.lean) and `digits_shape_at`
    with `place_digits` and `shapeZAll_of_public` (Johnson/Desc/First/Look/DigitsShapeAt.lean).
  `shapeIsFs_of_public`: **conditional on hX: `ShapeIsFs Z.p.X s` at every site s of Z.**
  `shapeIsFs_test_of_public`: **the same of the test: `shapeIsFs Z.p.X s = true`.**
  `shapeIsFs_head`: both, conditional on `P5J.AtMgA`: hX is the head's own field `pubOne`.

Hypotheses that remain. hX: `Verify.publicOf pol KL layout = .ok Z.p.X`: on public data alone. In
the last: h: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`. Conditional on the head `P5J.AtMgA`. That
it holds at the goals' two named sets of public files is a sealed theorem (`headMember_named`,
AtFullSide/Top/HeadMemberAtGap.lean), with that file's own limits; this file does not call it. No
hypothesis is made on the site's caller, sort or link.

Kin. Another house's `shape_layers_at` (Johnson/AtFull/Shape/LookFree.lean)
says under `P5J.AtMgA`, at a site on the calls of a layers' link:
`s.shape = Zp.p.X.y.fo`. `fs_layers` (Honest/K3/Law/Thread/PutFo.lean) says, at such a site,
`fsOf Z.p.X s = some Z.p.X.y.fo`; `ShapeIsFs` says `fsOf Z.p.X s = some s.shape`. That the two
together give the other house's equation is not typed here. `fits_gives`
(Honest/K3/Law/SeatFitsLaw.lean) yields the test's yes from an acceptance by `k3Fits`.

Limits. Public data alone. Not what the shape's numbers are. Nothing at a record that
`Verify.publicOf` did not return. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Out
import Johnson.Desc.ProofFile.Honest.K3.LotPublic
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (P placeAt lookAt lay_shape att_shape head_shape
  place_digits digits_shape_at shapeZAll_of_public)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- Conditional on hX: the shape that a place's parameters fix is the place's own `fs`: at every
link, on the calls and on the digits. -/
theorem place_shape_fs {pol KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hX : OnBytes.Model.Verify.publicOf pol KL layout = .ok X)
    (i : Nat) (dg : Bool) (x : VerifiableInference.Desc.First.Look.Place)
    (hx : lookAt X i dg = some x) (set : OnBytes.Params.Setting) :
    (P.ofPlace set dg x).shape = some x.fs := by
  cases dg with
  | true =>
    obtain ⟨tl, ht, _, _, _, e⟩ := place_digits hx
    rw [e]
    exact digits_shape_at (shapeZAll_of_public hX) hx ht set
  | false =>
    by_cases hn : i = (if X.p4 then 2 else 1) * X.NGr
    · subst hn
      exact head_shape set hX hx
    · by_cases h0 : i % (if X.p4 then 2 else 1) = 0
      · exact lay_shape set hX hx hn h0
      · exact att_shape set hX hx hn h0

/-- **Conditional on hX: the site's shape is the shape that the plan itself holds for it: at every
site.** -/
theorem shapeIsFs_of_public {pol KL : ByteArray} {layout : Option ByteArray} {Z : Pub}
    (hX : OnBytes.Model.Verify.publicOf pol KL layout = .ok Z.p.X) (s : Site)
    (hs : s ∈ lookSites Z) : ShapeIsFs Z.p.X s := by
  unfold lookSites at hs
  obtain ⟨a, _, ha⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, _⟩ := site_facts _ _ a s ha
  rw [← f3, ← f4] at f1
  unfold placeAt at f1
  obtain ⟨x, hx, hp⟩ := Option.map_eq_some_iff.1 f1
  have e := place_shape_fs hX s.link s.digits x hx (OnBytes.Params.settingOf Z.p.X.P.frame)
  rw [hp, f2] at e
  unfold ShapeIsFs fsOf
  rw [hx, Option.map_some, ← Option.some.inj e]

/-- **The same of the test with code.** -/
theorem shapeIsFs_test_of_public {pol KL : ByteArray} {layout : Option ByteArray} {Z : Pub}
    (hX : OnBytes.Model.Verify.publicOf pol KL layout = .ok Z.p.X) (s : Site)
    (hs : s ∈ lookSites Z) : shapeIsFs Z.p.X s = true := by
  have e : fsOf Z.p.X s = some s.shape := shapeIsFs_of_public hX s hs
  unfold shapeIsFs
  rw [e]
  exact sameShapeAll_refl s.shape

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Both, conditional on `P5J.AtMgA`. -/
theorem shapeIsFs_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : ShapeIsFs Zp.p.X s ∧ shapeIsFs Zp.p.X s = true :=
  ⟨shapeIsFs_of_public h.toAtMg.pubOne s hs, shapeIsFs_test_of_public h.toAtMg.pubOne s hs⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.place_shape_fs
#print axioms ProofFile.Honest.K3.Law.AtThr.shapeIsFs_of_public
#print axioms ProofFile.Honest.K3.Law.AtThr.shapeIsFs_test_of_public
#print axioms ProofFile.Honest.K3.Law.AtThr.shapeIsFs_head
