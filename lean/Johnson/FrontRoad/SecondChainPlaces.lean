-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SecondChainPlaces.lean: the proofs of the five statements of
Johnson/FrontRoad/SecondChainPlacesSpec.lean: at all letters the second chain of the description
descZ Zp Np cF has four members, none of the kind K8; so the pin at the second chain is a condition
on the halves that stand at its four places alone.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The five proofs   second_places_at, no_k8_second, pin_none_iff, pin_second_iff,
      pin_none_needs_no_k8.

How it fits. second_places_at goes as the last lines of the proof of second_places
(Johnson/Desc/ProofFile/Law/LaterKinds.lean) do, at the seat secondAt Zp Np, which descZ has by
name; it calls that file's k12_place and p12At_place. All limits: the head of
Johnson/FrontRoad/SecondChainPlacesSpec.lean. Not one of the release's goal statements.
-/
import Johnson.FrontRoad.SecondChainPlacesSpec
import Johnson.Desc.ProofFile.Law.LaterKinds

set_option autoImplicit false

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles (descZ)
open VerifiableInference.Desc (Block Place KindName)
open P5J (TS)

theorem second_places_at : Spec.second_places_at := by
  intro Zp Np cF
  have e : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) : Block VerifiableInference.Desc.K12.T12 Unit).place =
      ⟨3, none, 2, .K12⟩ := by
    rw [ProofFile.Law.k12_place, ProofFile.Law.p12At_place]
  show [(⟨3, none, 0, .K14⟩ : Place), ⟨3, none, 1, .frame⟩,
    { (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
        (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) :
          Block VerifiableInference.Desc.K12.T12 Unit).place with
      chain := 3, link := none, piece := 2 }, ⟨3, none, 3, .frame⟩] = _
  rw [e]
  rfl

theorem no_k8_second : Spec.no_k8_second := by
  intro Zp Np cF b hb hk
  have hm : b.place ∈ secondPlacesW := by
    rw [← second_places_at Zp Np cF]
    exact List.mem_map_of_mem hb
  unfold secondPlacesW at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e <;> rw [e] at hk <;> cases hk

theorem pin_none_iff : Spec.pin_none_iff := by
  intro S Cl W₀ Rc Xi Tr X cells hs bs
  constructor
  · intro h
    have h' : ∀ b ∈ bs, b.place.kind ≠ KindName.K8 ∧
        ∀ g, (hs.find? fun g => g.place == b.place) = some g →
          ∀ p ∈ g.parts, (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0 := h
    exact ⟨fun b hb => (h' b hb).1, fun b hb => (h' b hb).2⟩
  · intro h b hb
    show b.place.kind ≠ KindName.K8 ∧
      ∀ g, (hs.find? fun g => g.place == b.place) = some g →
        ∀ p ∈ g.parts, (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0
    exact ⟨h.1 b hb, h.2 b hb⟩

theorem pin_second_iff : Spec.pin_second_iff := by
  intro Zp Np cF W₀ Rc Xi Tr X cells hs
  rw [pin_none_iff cells hs]
  exact ⟨fun h => h.2, fun h => ⟨no_k8_second Zp Np cF, h⟩⟩

theorem pin_none_needs_no_k8 : Spec.pin_none_needs_no_k8 := by
  intro S Cl W₀ Rc Xi Tr X cells bs b hb hk
  refine ⟨fun b' _ g hg => ?_, fun h => ?_⟩
  · cases hg
  · exact ((pin_none_iff cells _ bs).1 h).1 b hb hk

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.second_places_at
#print axioms OnBytes.FrontRoad.no_k8_second
#print axioms OnBytes.FrontRoad.pin_none_iff
#print axioms OnBytes.FrontRoad.pin_second_iff
#print axioms OnBytes.FrontRoad.pin_none_needs_no_k8
