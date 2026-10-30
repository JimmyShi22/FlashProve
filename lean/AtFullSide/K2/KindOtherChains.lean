-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KindOtherChains.lean: the kind "the code switch" (K2) has no place in the shared chain
and none in the last chain.

  noKindW          by Lean's kernel, of the written description
  noKindW_bent     a control: the first chain has places of the kind
  others_no_kind   where the maker returns under the head, at any filling, no side of the shared or
                   the last chain stands at a place of the kind

Limits. Public numbers. Of places alone.
-/
import AtFullSide.K14.MakersBookOne
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Chain alike₂_place)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS F0T)

set_option maxRecDepth 1000000 in
/-- The written description has no place of the kind in its shared and last chains. -/
theorem noKindW : (WP.shared.blocksInOrder.all fun b => b.place.kind != .K2) = true ∧
    (WP.second.blocksInOrder.all fun b => b.place.kind != .K2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the like test at the first chain says no. -/
theorem noKindW_bent : (WP.first.blocksInOrder.all fun b => b.place.kind != .K2) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- Where no side strays and no place of the chain has the kind, no side has it. -/
theorem no_kind_of_chain {S C V W X : Type} (bs : List (VerifiableInference.Desc.Block S C))
    (hs : List (Placed V W X)) (t : (strays bs hs).isEmpty = true)
    (hb : ∀ a ∈ bs.map (·.place), a.kind ≠ .K2) :
    hs.filter (fun x => x.place.kind == .K2) = [] := by
  refine List.filter_eq_nil_iff.2 fun x hx hk => ?_
  cases h0 : bs.any fun b => b.place == x.place with
  | false =>
    have hm : x.place ∈ strays bs hs := by
      refine List.mem_map_of_mem (List.mem_filter.2 ⟨hx, ?_⟩)
      show (!(bs.any fun b => b.place == x.place)) = true
      rw [h0]
      rfl
    rw [List.isEmpty_iff.1 t] at hm
    cases hm
  | true =>
    obtain ⟨b, hb', e⟩ := List.any_eq_true.1 h0
    have e' : b.place = x.place := beq_iff_eq.1 e
    exact hb x.place (e' ▸ List.mem_map_of_mem hb') (beq_iff_eq.1 hk)

/-- **No side of the two other chains stands at a place of the kind.** -/
theorem others_no_kind (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.H.shared.filter (fun x => x.place.kind == .K2) = [] ∧
      A.H.second.filter (fun x => x.place.kind == .K2) = [] := by
  obtain ⟨B, -, -, -, -, hAll⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨-, eF⟩ := hAll _ _ _ _ _ P A hA
  obtain ⟨-, -, t2, t3, -⟩ := atPure_tests hA
  have pa := planAlike_at_head h
  have e2 : A.F.shared.blocksInOrder.map (·.place) = WP.shared.blocksInOrder.map (·.place) :=
    (congrArg (fun F : VerifiableInference.Desc.FileDescription ProofFile.Inst =>
      F.shared.blocksInOrder.map (·.place)) eF).trans (alike₂_place _ _ pa.shared).symm
  have e3 : A.F.second.blocksInOrder.map (·.place) = WP.second.blocksInOrder.map (·.place) :=
    (congrArg (fun F : VerifiableInference.Desc.FileDescription ProofFile.Inst =>
      F.second.blocksInOrder.map (·.place)) eF).trans (alike₂_place _ _ pa.second).symm
  refine ⟨no_kind_of_chain _ _ t2 fun a ha hk => ?_, no_kind_of_chain _ _ t3 fun a ha hk => ?_⟩
  · rw [e2] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have hw := List.all_eq_true.1 noKindW.1 b hb
    rw [hk] at hw
    exact absurd hw (by decide)
  · rw [e3] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have hw := List.all_eq_true.1 noKindW.2 b hb
    rw [hk] at hw
    exact absurd hw (by decide)

end AtFullSide.K2

#print axioms AtFullSide.K2.noKindW
#print axioms AtFullSide.K2.noKindW_bent
#print axioms AtFullSide.K2.no_kind_of_chain
#print axioms AtFullSide.K2.others_no_kind
