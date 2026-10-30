-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3More.lean: WHAT IS LEFT OF A LINK's LAW (K9): THE FIELDS k3d, k3g,
k3f OF `SortRest` (SortRest.lean) AT THE ENTRIES "objects" AND "planes": PAID, IN
THE GOALS' SCOPE. Theorems: calls, two each. IT PAYS NO LAW OF ITS OWN.

THE BARE RUNS' THREE ARE THE LOOKUP's FILES' (Johnson/Top/H/Keep/PutsMore.lean): objects_more |
planes_more : PutsMore ‹the run› under AtS2 seat alone, and for any run with PutsMore:
keepsDoor_of_more · good9_of_more · numOf_of_more u. HERE THEY ARE CALLED BEHIND THE TIES
at_objects_is (SortK3Objects.lean) | at_planes_is (SortK3Planes.lean).

  k3d_objects · k3g_objects · k3f_objects   at (IM.k3Ix m d, "objects")
  k3d_planes · k3g_planes · k3f_planes      at (IM.k3Ix m false, "planes"), where the readers are
                                            there (hr)
  k3d_layers · k3g_layers · k3f_layers      at a layers' link (m ≠ 24): the three fields whole, in
                                            the fields' own texts

PREMISES: hS hR O · m < 25 · hL : c.links[m]? = some L · at "planes" hr.
Limits. NO MEMBER: no state is shown at which a run says yes. Nothing on "join". Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Top.H.Keep.PutsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (KeepsDoor good9 numOf)
open VerifiableInference.Desc.LinkJoin (At)

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
  (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
  {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
include hS hR O hm hL

/-! ## "objects" -/

/-- **k3d at "objects".** -/
theorem k3d_objects (d : Bool) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → KeepsDoor atS e e₁ := by
  rw [at_objects_is hS hR O hm d hL h]
  exact keepsDoor_of_more (objects_more _ (atS2_seatOf d))

/-- **k3g at "objects".** -/
theorem k3g_objects (d : Bool) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → good9 e → good9 e₁ := by
  rw [at_objects_is hS hR O hm d hL h]
  exact good9_of_more (objects_more _ (atS2_seatOf d))

/-- **k3f at "objects".** -/
theorem k3f_objects (d : Bool) (u : HTailF2) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → numOf u e₁ = numOf u e := by
  rw [at_objects_is hS hR O hm d hL h]
  exact numOf_of_more (objects_more _ (atS2_seatOf d)) u

/-! ## A layers' link: the three fields whole -/

theorem k3d_layers (h24 : m ≠ 24) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e cl e₁, run n e = .ok (cl, e₁) → KeepsDoor atS e e₁ := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3d_objects hS hR O hm hL d run h

theorem k3g_layers (h24 : m ≠ 24) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e cl e₁, run n e = .ok (cl, e₁) → good9 e → good9 e₁ := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3g_objects hS hR O hm hL d run h

theorem k3f_layers (h24 : m ≠ 24) (u : HTailF2) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e cl e₁, run n e = .ok (cl, e₁) → numOf u e₁ = numOf u e := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3f_objects hS hR O hm hL d u run h

/-! ## "planes" -/

section
variable {r : Desc.K3.Readers S} (hr : K3Lot.readersAt Bs.G₀.W m = some r)
include hr

/-- **k3d at "planes".** -/
theorem k3d_planes (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → KeepsDoor atS e e₁ := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  exact keepsDoor_of_more (planes_more _ k03_atS2_calls p.lm r)

/-- **k3g at "planes".** -/
theorem k3g_planes (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → good9 e → good9 e₁ := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  exact good9_of_more (planes_more _ k03_atS2_calls p.lm r)

/-- **k3f at "planes".** -/
theorem k3f_planes (u : HTailF2) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → numOf u e₁ = numOf u e := by
  obtain ⟨p, _, rfl⟩ := at_planes_is hS hR O hm hL hr h
  exact numOf_of_more (planes_more _ k03_atS2_calls p.lm r) u

end

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3d_objects
#print axioms VerifiableInference.OnPublicFiles.k3g_objects
#print axioms VerifiableInference.OnPublicFiles.k3f_objects
#print axioms VerifiableInference.OnPublicFiles.k3d_layers
#print axioms VerifiableInference.OnPublicFiles.k3g_layers
#print axioms VerifiableInference.OnPublicFiles.k3f_layers
#print axioms VerifiableInference.OnPublicFiles.k3d_planes
#print axioms VerifiableInference.OnPublicFiles.k3g_planes
#print axioms VerifiableInference.OnPublicFiles.k3f_planes
