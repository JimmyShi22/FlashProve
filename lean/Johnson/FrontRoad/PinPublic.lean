-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/PinPublic.lean: the proofs of the eleven statements of
Johnson/FrontRoad/PinPublicSpec.lean: the pin is a condition on public data and a condition on the
halves; the first holds at the first chain of the proof file's description without its last member,
at the description's own parameters and the list matsOf, and at the second chain, at the par that
names none.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The steps   k8AllB_placesW: a closed fact on the written list of places, by evaluation in Lean's
      kernel: every entry of the kind K8 stands at a number ixOf l with l ≤ 24 (the test k8AllB,
      Johnson/P1K8R/Tied.lean; that file has the like at a list that is written otherwise).
      k8_at_placesW: the same as a statement; its proof goes as that of k8_places_full there.
      member_at, k8_member: the places of the kind K8 among the first chain's members without the
      last are just the written places k8PlaceAt l, l < 25, member by member; from k8_places_front
      (Johnson/FrontRoad/ParOwnChecks.lean).
  The eleven proofs   pin_iff, halves_none_iff, pin_first_public, public_first, public_second,
      pin_first_iff, halves_first_iff, wrong_rounds_not_public, unfit_not_public,
      halves_need_no_public, short_names_not_public.

How it fits. pin_first_public: a member of the first chain has a number in its flat list; place_at
(Johnson/IMR/PlacesScope.lean) finds its place at that number of the written list; k8_at_placesW
makes the number ixOf l; parOwn_at_draw (Johnson/FrontRoad/ParOwn.lean) has the parameters and the
one round at that number. public_first adds smallFits, by fits_iff_length, tl_is_plan and plan_size
(Johnson/FrontRoad/CellsAreTrace.lean); that the link is below 25 comes from ground_gets
(Johnson/IMR/PureJoin.lean). All limits: the head of Johnson/FrontRoad/PinPublicSpec.lean. Not one
of the release's goal statements.
-/
import Johnson.FrontRoad.PinPublicSpec
import Johnson.FrontRoad.CellsAreTrace
import Johnson.FrontRoad.SecondChainPlaces
import Johnson.P1K8R.Tied
import Johnson.IMR.PureJoin

set_option autoImplicit false

namespace OnBytes.FrontRoad
open VerifierAndGoals (PublicFiles InScope readFiles)
open P5J (TS LaidAt)
open OnBytes.Maker (WholeD)
open AtPublicFiles.AtFiles (descZ)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par round)
open OnBytes.HonestTrace (matsOf)
open ProofFile.Honest (Placed Local Cells)
open ProofFile.Honest.K8 (smallStop smallFits windowShare)
open ProofFile.Honest.K9 (quietStop)

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/-! ## The steps -/

set_option maxRecDepth 1000000 in
/-- In the written list of places every entry of the kind K8 stands at a number ixOf l, l ≤ 24: the
test says yes. placesW is a closed term, which the kernel evaluates. -/
theorem k8AllB_placesW : P1K8T.k8AllB IM.placesW = true := by decide +kernel

/-- Where the kind K8 stands in the written list of places: at the numbers ixOf l, l ≤ 24, alone. -/
theorem k8_at_placesW (i : ℕ) (a : Place) (ha : IM.placesW[i]? = some a)
    (hk : a.kind = KindName.K8) : ∃ l, l ≤ 24 ∧ i = P1K8T.ixOf l := by
  have hi : i < IM.placesW.length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k8AllB_placesW i (List.mem_range.2 hi)
  rw [ha] at h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [hk] at h1
    exact absurd h1 (by decide)
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h1
    exact ⟨l, Nat.le_of_lt_succ (List.mem_range.1 hl), by simpa using e⟩

/-! ## The eleven -/

theorem pin_iff : Spec.pin_iff := by
  intro S Cl W₀ Rc Xi Tr X par cells hs bs
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro b hb
      have h' := h b hb
      cases hp : par b.place with
      | none =>
        rw [hp] at h'
        exact h'.1
      | some P =>
        rw [hp] at h'
        obtain ⟨g, -, hf, hr, -⟩ := h'
        exact ⟨hf, hr⟩
    · intro b hb
      have h' := h b hb
      cases hp : par b.place with
      | none =>
        rw [hp] at h'
        exact h'.2
      | some P =>
        rw [hp] at h'
        obtain ⟨g, hg, -, -, hq⟩ := h'
        exact ⟨g, hg, hq⟩
  · intro h b hb
    have h1 := h.1 b hb
    have h2 := h.2 b hb
    cases hp : par b.place with
    | none =>
      rw [hp] at h1 h2
      exact ⟨h1, h2⟩
    | some P =>
      rw [hp] at h1 h2
      obtain ⟨g, hg, hq⟩ := h2
      exact ⟨g, hg, h1.1, h1.2, hq⟩

theorem halves_none_iff : Spec.halves_none_iff := by
  intro S Cl W₀ Rc Xi Tr X cells hs bs
  exact Iff.rfl

theorem pin_first_public : Spec.pin_first_public := by
  intro Z Zp Np cF scope pp hr D r L mats b hb hk
  obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.1 (List.mem_of_mem_dropLast hb)
  obtain ⟨Bs, base, O⟩ := L.opened
  have hp : IM.placesW[k]? = some b.place := IM.place_at scope hr O hk'
  obtain ⟨l, hl, rfl⟩ := k8_at_placesW k b.place hp hk
  obtain ⟨b', G₀, Xl, eb, -, -, -, hpar, hr'⟩ := parOwn_at_draw Z Zp Np cF scope hr L mats hl
  obtain rfl : b' = b := Option.some.inj (eb.symm.trans hk')
  exact ⟨_, hpar, hr'⟩

theorem public_first : Spec.public_first := by
  intro Z Zp Np cF scope pp hr D r L b hb
  cases hp : parOwn Zp (matsOf Zp.p.X) b.place with
  | none =>
    intro hk
    obtain ⟨P, hP, -⟩ := pin_first_public Z Zp Np cF scope hr L (matsOf Zp.p.X) b hb hk
    rw [hp] at hP
    cases hP
  | some P =>
    obtain ⟨hk, l, G₀, Xl, -, hG, hX, rfl⟩ := parOwn_some Zp _ b.place P hp
    obtain ⟨P', hP', hr'⟩ := pin_first_public Z Zp Np cF scope hr L (matsOf Zp.p.X) b hb hk
    rw [hp] at hP'
    obtain rfl := Option.some.inj hP'
    have h25 : G₀.built.size = 25 := (IM.ground_gets scope hr L.pub hG).1
    have hl : l < 25 := h25 ▸ (Array.getElem?_eq_some_iff.1 hX).1
    refine ⟨?_, hr'⟩
    rw [fits_iff_length, tl_is_plan Z Zp Np cF scope hr L hG hl hX,
      plan_size Z Zp Np cF scope hr L hl]
    exact beq_self_eq_true _

theorem public_second : Spec.public_second := by
  intro Zp Np cF b hb
  exact no_k8_second Zp Np cF b hb

theorem pin_first_iff : Spec.pin_first_iff := by
  intro Z Zp Np cF scope pp hr D r L W₀ Rc Xi Tr X cells hs
  rw [pin_iff]
  exact ⟨fun h => h.2, fun h => ⟨public_first Z Zp Np cF scope hr L, h⟩⟩

/-- Each written place k8PlaceAt l, l < 25, is the place of a member of the first chain without its
last member. -/
theorem member_at (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) (scope : InScope Z = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {l : ℕ} (hl : l < 25) :
    ∃ b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast, b.place = k8PlaceAt l := by
  have h := (k8_places_front Z Zp Np cF scope hr L).1
  have hm : k8PlaceAt l ∈ (List.range 25).map k8PlaceAt :=
    List.mem_map_of_mem (List.mem_range.2 hl)
  rw [← h] at hm
  obtain ⟨b, hb, e⟩ := List.mem_map.1 (List.mem_filter.1 hm).1
  exact ⟨b, hb, e⟩

/-- The place of a member of the kind K8 of the first chain without its last member is one of the
written places k8PlaceAt l, l < 25. -/
theorem k8_member (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) (scope : InScope Z = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {b : Block TS ProofFile.Cl} (hb : b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (hk : b.place.kind = KindName.K8) : ∃ l < 25, b.place = k8PlaceAt l := by
  have h := (k8_places_front Z Zp Np cF scope hr L).1
  have hm : b.place ∈ ((descZ Zp Np cF).first.blocksInOrder.dropLast.map (·.place)).filter
      (fun a => a.kind == KindName.K8) :=
    List.mem_filter.2 ⟨List.mem_map_of_mem hb, by rw [hk]; rfl⟩
  rw [h] at hm
  obtain ⟨l, hl, e⟩ := List.mem_map.1 hm
  exact ⟨l, List.mem_range.1 hl, e.symm⟩

theorem halves_first_iff : Spec.halves_first_iff := by
  intro Z Zp Np cF scope pp hr D r L W₀ Rc Xi Tr X cells hs
  constructor
  · intro h
    refine ⟨fun l hl => ?_, fun b hb g hg => ?_⟩
    · obtain ⟨G₀, Xl, -, -, hP, -⟩ := matsOf_fits Z Zp Np cF scope hr L l hl
      obtain ⟨b, hb, e⟩ := member_at Z Zp Np cF scope hr L hl
      have h' := h b hb
      rw [e, hP] at h'
      obtain ⟨g, hg, hq⟩ := h'
      exact ⟨_, g, hP, hg, hq⟩
    · obtain ⟨hb', hk⟩ := List.mem_filter.1 hb
      have hk' : b.place.kind ≠ KindName.K8 := by simpa using hk
      have h' := h b hb'
      rw [parOwn_other Zp _ b.place hk'] at h'
      exact h' g hg
  · intro h b hb
    by_cases hk : b.place.kind = KindName.K8
    · obtain ⟨l, hl, e⟩ := k8_member Z Zp Np cF scope hr L hb hk
      obtain ⟨P, g, hP, hg, hq⟩ := h.1 l hl
      rw [e, hP]
      exact ⟨g, hg, hq⟩
    · rw [parOwn_other Zp _ b.place hk]
      exact h.2 b (List.mem_filter.2 ⟨hb, by simpa using hk⟩)

theorem wrong_rounds_not_public : Spec.wrong_rounds_not_public := by
  intro S Cl par bs b P hb hp hne h
  have h' := h b hb
  rw [hp] at h'
  exact hne h'.2

theorem unfit_not_public : Spec.unfit_not_public := by
  intro S Cl par bs b P hb hp hf h
  have h' := h b hb
  rw [hp] at h'
  have hfit := h'.1
  rw [hf] at hfit
  cases hfit

theorem halves_need_no_public : Spec.halves_need_no_public := by
  intro S Cl W₀ Rc Xi Tr X par cells b P hp b' hb'
  rw [List.mem_singleton.1 hb', hp]
  refine ⟨⟨b.place, [quietStop (smallStop cells P) (windowShare P.1)]⟩, ?_, rfl⟩
  rw [List.find?_cons_of_pos]
  exact beq_self_eq_true _

theorem short_names_not_public : Spec.short_names_not_public := by
  intro Z Zp Np cF scope pp hr D r L h
  obtain ⟨Bs, base, O⟩ := L.opened
  have hG := O.blank
  obtain ⟨Xl, hX⟩ := built_at Z Zp Np cF scope hr L hG 0 (by norm_num)
  obtain ⟨b, hb, e⟩ := member_at Z Zp Np cF scope hr L (l := 0) (by norm_num)
  have h' := h b hb
  rw [e, parOwn_at Zp _ hG hX] at h'
  have hfit := h'.1
  rw [short_names_do_not_fit Z Zp Np cF scope hr L 0 (by norm_num) _ Xl hG hX] at hfit
  cases hfit

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.k8AllB_placesW
#print axioms OnBytes.FrontRoad.k8_at_placesW
#print axioms OnBytes.FrontRoad.pin_iff
#print axioms OnBytes.FrontRoad.halves_none_iff
#print axioms OnBytes.FrontRoad.pin_first_public
#print axioms OnBytes.FrontRoad.public_first
#print axioms OnBytes.FrontRoad.public_second
#print axioms OnBytes.FrontRoad.pin_first_iff
#print axioms OnBytes.FrontRoad.member_at
#print axioms OnBytes.FrontRoad.k8_member
#print axioms OnBytes.FrontRoad.halves_first_iff
#print axioms OnBytes.FrontRoad.wrong_rounds_not_public
#print axioms OnBytes.FrontRoad.unfit_not_public
#print axioms OnBytes.FrontRoad.halves_need_no_public
#print axioms OnBytes.FrontRoad.short_names_not_public
