-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPServedLaws.lean: where the served requests sit. It states no goal.

  servedRequest_isTrue   a served request is true under the files' policy at the weights' index:
    ServedRequest lies inside yesAt.
  servedRequest_below   and so it lies in the object's relation RyesZ.
  servedRequest_met   in scope there is a served request, at made-up weights.
-/
import E2E.CompleteAsIOPAtFiles
import IntegerModel.Arrays.RequestResultLaws
import Johnson.FrontRoad.TieServed

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open VerifiableInference (canServe_and_modelOutput_iff)
open VerifierAndGoals (PublicFiles InScope readFiles settingsOfRead valid_of_read)
open FlashProve (backB build_home_of_built homeR served_home xAt yesAt)

variable (b : PublicFiles → ℕ) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}

/-- **A served request is true under the files' policy.** -/
theorem servedRequest_isTrue (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    {i : (homeR b Z).Index} {x : (homeR b Z).Instance} (h : ServedRequest b Z hr i x) : yesAt b Z hr i x := by
  obtain ⟨w, p, o, rfl, hform, hres, hb⟩ := h
  obtain ⟨hd, hm⟩ := (canServe_and_modelOutput_iff (valid_of_read hr) w p o).2 ⟨hform, hres⟩
  obtain ⟨hb', hy⟩ := served_home b Z scope hr x w p o hd hm
  have e : xAt b Z x p o = x := Option.some.inj (hb'.symm.trans hb)
  rwa [e] at hy

/-- **A served request is in the object's relation.** -/
theorem servedRequest_below (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    {i : (homeR b Z).Index} {x : (homeR b Z).Instance} (h : ServedRequest b Z hr i x) :
    AtPublicFiles.Committed.RyesZ Z i x :=
  OnBytes.FrontRoad.yesAt_below_object b Z hr i x (servedRequest_isTrue b Z scope hr h)

/-- **In scope there is a served request.** -/
theorem servedRequest_met (scope : InScope Z = true) (hr : readFiles Z = .ok pp) :
    ∃ i x, ServedRequest b Z hr i x := by
  obtain ⟨w, p, o, hd, hm⟩ := Meaning.served_met hr
  obtain ⟨hform, hres⟩ := (canServe_and_modelOutput_iff (valid_of_read hr) w p o).1 ⟨hd, hm⟩
  obtain ⟨x, hx, -⟩ := Meaning.true_of_served scope hr w p o hd hm
  exact ⟨backB b Z (settingsOfRead pp) w, _, w, p, o, rfl, hform, hres, build_home_of_built b Z hx⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.servedRequest_isTrue
#print axioms AtPublicFiles.AtFiles.servedRequest_below
#print axioms AtPublicFiles.AtFiles.servedRequest_met
