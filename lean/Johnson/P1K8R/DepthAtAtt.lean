-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/DepthAtAtt.lean: UNDER THE DESCRIPTION's HEAD, ON PUBLIC NUMBERS ALONE: AT EACH OF THE
TWELVE ATTENTION SEGMENTS THE SHAPE OF THE LOOKUP ON THE SEGMENT's CALLS, AS THE HONEST SIDE's LIST
OF SITES HAS IT, IS THE PLAN's, AND ITS TREES HAVE DEPTH lmS AT LEAST. No state, no run, no
challenge. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `site_made_place`   site_facts (Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean)
  **`lmS_le_depth`**   law_at_head, public_at_head (Johnson/Desc/K5/Honest/Law/PublicAtHead.lean);
      OnBytes.Road.Rows.norm_of_hid (Johnson/Road/Rows/AttReadLong.lean)
  **`site_shape_att`**   Att.P.guard_theorems (Johnson/Desc/First/Att/GuardPlan.lean);
      H2K5.Door.planIs_all, scope_all (Johnson/Desc/First/Att/Door/Law/)
  **`depth_at_att`**   the two
Kin. A TWIN BUT FOR ONE PROJECTION: the lookups' authors' site_fs_att_head
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AttBackHead.lean): the same head, site, link, sort and
plan: s.p.shape = some a.fs, by the same Att.P.guard_theorems: with their site_made_shape
(SitesOk.lean) it is `site_shape_att`. Not called: that file does not lie beneath this one. Their
calls_att (K3/Good/Live/Windows.lean) has the same shape at the library's own parameters.
`site_made_place` is the first four clauses of their site_facts (K3/Law/MemberSite.lean): called;
`site_pars` (Johnson/P1K8R/ClausesAtFrame.lean) draws the same four. `PlanR.lmS`
(Johnson/Desc/K5/Honest/Law/LookR.lean) is `lmS_le_depth`'s sentence as a field of a premise's form;
we have seen no proof of that structure anywhere. fo_at_head (FoAtHead.lean): the plan's shape
passes the library's test and has four calls: by the same place.
Limits. The head h is a hypothesis; the full size alone. It stands over files of the kinds "lookup"
and "attention's own rounds" on the honest side.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SitesOk
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Desc.First.Att.GuardPlan
import Johnson.Desc.First.Att.Door.Law.K5AtConstant
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Road.Rows.AttReadLong

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest.K3 (Site siteAt lookSites)
open H2K5.Honest (law_at_head public_at_head)
open P5J (AtMgA TS)

/-- At a site s that `siteAt` makes, the library's `placeAt` at s's link and at s.digits returns
s.p, and s.p's shape is s.shape: out of the first four clauses of site_facts
(Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean). -/
theorem site_made_place (X : OnBytes.Model.Verify.Public) (ps : List _)
    (x : Nat × Bool × Place) (s : Site) (hs : siteAt X ps x = some s) :
    Look.placeAt X s.link s.digits = some s.p ∧ s.p.shape = some s.shape := by
  obtain ⟨f1, f2, f3, f4, -⟩ := ProofFile.Honest.K3.Law.site_facts X ps x s hs
  rw [f3, f4]
  exact ⟨f1, f2⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
include h

/-- **A tree of the lookup on an attention segment's calls is deep enough for a column of the
scores' matrix**: lmS is at most dT, at the group's plan. As the sealed
Johnson/Desc/First/Att/K05ReturnsAt.lean comes to the like inside a proof. -/
theorem lmS_le_depth {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) : (Att.P.parCOf a).geo.lmS ≤ a.fs.dT := by
  obtain ⟨hid, PL⟩ := law_at_head h hg ea
  have N := OnBytes.Road.Rows.norm_of_hid hid
  have e : (OnBytes.Road.L5.dimOf a.S).lD = a.S.nD := N.nD.symm
  have fD : (OnBytes.Road.L5.dimOf a.S).lD ≤ (OnBytes.Road.L5.callsOf a.fs).Dk :=
    PL.fit.2.2.2.2.2.2.1.2.1
  have hZ : a.S.cf.lmS ≤ a.S.nD := (public_at_head h hg ea).sized.Z.lmS
  rw [e] at fD
  exact le_trans hZ fD

/-- **The shape of the site of the lookup on an attention segment's calls is the plan's.** -/
theorem site_shape_att {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    ∀ s ∈ lookSites Zp, s.link = 2 * g + 1 → s.digits = false → s.shape = a.fs := by
  intro s hs el hd
  unfold lookSites at hs
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hs
  obtain ⟨hp, hsh⟩ := site_made_place _ _ x s hx
  rw [el, hd] at hp
  unfold Look.placeAt at hp
  obtain ⟨x₁, hx₁, e⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨k1, -, k3, -⟩ := Att.P.guard_theorems (H2K5.Door.planIs_all h)
    (H2K5.Door.scope_all h).1 ea hx₁ (Params.settingOf Zp.p.X.P.frame)
  rw [e, hsh, k3] at k1
  exact Option.some.inj k1

/-- **SO: THE SENTENCE ON PUBLIC NUMBERS THAT `attLive_handed` (Johnson/P1K8R/AttLiveAtFrame.lean)
ASKS AS hdT.** -/
theorem depth_at_att {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) :
    ∀ s ∈ lookSites Zp, s.link = 2 * g + 1 → s.digits = false →
      (Att.P.parCOf a).geo.lmS ≤ s.shape.dT := by
  intro s hs el hd
  rw [site_shape_att h ea s hs el hd]
  exact lmS_le_depth h hg ea

end

end P1K8

#print axioms P1K8.site_made_place
#print axioms P1K8.lmS_le_depth
#print axioms P1K8.site_shape_att
#print axioms P1K8.depth_at_att
