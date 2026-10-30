-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- where the rows of the kinds K10, K12 and K14 stand at `theGOfReturn`.
/-
AtFullSide/M1/KindRowsTheG.lean: the memberships inside `kindPays_K10_sides`, `kindPays_K14_sides`, and K12's at L, as
statements on the lists of `theGOfReturn made hd T K`, at any K that holds ours. The clauses «none» say
more than that a chain has no block of the kind: no list of the kind stands in G. No property of the
protocol is claimed here.
-/
import AtFullSide.M1.KLarger
import AtFullSide.M1.K12AtG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)

/-- **No lot lays a half of the kind K14 on the first chain.** -/
theorem lots_k14 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ baseFill.lots, ∀ g ∈ M.halves Z G, g.place.kind ≠ KindName.K14 := by
  intro M hM g hg e
  have hM' : M ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest).lots := hM
  rw [widerFillAtCPUOWM_lots] at hM'
  simp only [List.mem_append, List.mem_singleton] at hM'
  rcases hM' with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hk := (FirstFill.widerKinds matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest
      Z G).all q hq g hg
    rw [e] at hk
    have hno : KindName.K14 ∉ (widerPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
        openHonest).map (·.2) := by
      simp [widerPairs]
    exact hno (List.mem_map.2 ⟨q, hq, hk.symm⟩)
  · have hk := closeLotAt_kinds matrixInput OnBytes.HonestTrace.Sz.ref Z G g hg
    rw [e] at hk
    cases hk
  · have hk := proxLotAt_kinds matrixInput OnBytes.HonestTrace.Sz.ref Z G g hg
    rw [e] at hk
    cases hk
  · have hk := AtFullSide.K12.wHalf_place matrixInput OnBytes.secondHashFunction openHonest Z G g hg
    rw [hk] at e
    cases e

variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- A list of the first chain of `theG` is a row laid over a lot of the filling. -/
theorem first_row_of (hd : HeadAtReturn files A₀) (T : ThreadParts A₀ Wt)
    (K : KindRows baseFill A₀.Z A₀.G) :
    ∀ L ∈ (theG hd T K).first, ∃ M ∈ baseFill.lots,
      L.bare ∈ (overlayLot K.lots M).rows A₀.Z A₀.G ∧ L.bare.half ∈ M.halves A₀.Z A₀.G := by
  intro L hL
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hl
  refine ⟨M, hM, hrl, ?_⟩
  show r.half ∈ _
  rw [← overlay_half (K.lots_fit M hM)]
  exact List.mem_map.2 ⟨r, hrl, rfl⟩

/-- A list of the shared chain of `theG` has a side of the filling as its half. -/
theorem shared_row_of (hd : HeadAtReturn files A₀) (T : ThreadParts A₀ Wt)
    (K : KindRows baseFill A₀.Z A₀.G) :
    ∀ L ∈ (theG hd T K).shared, L.bare ∈ K.slots.shared ∧
      L.bare.half ∈ baseFill.shared A₀.Z A₀.G := by
  intro L hL
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  exact ⟨hr, slot_row_half K.shared_fit r hr⟩

/-- The filling's shared sides are of the kinds K14, K1, K12. -/
theorem shared_kinds (hd : HeadAtReturn files A₀) :
    ∀ x ∈ baseFill.shared A₀.Z A₀.G, x.place.kind = KindName.K14 ∨ x.place.kind = KindName.K1 ∨
      x.place.kind = KindName.K12 := by
  intro x hx
  have hx' : x ∈ (sharedOurs A₀.Z hd.places A₀.G).map (·.half) := by
    rw [shared_fit hd.head]
    exact hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx'
  rcases List.mem_append.1 hr with h1 | h1
  · have e := ProofFile.Honest.K14.simRows_places (Ky := TableKey) (X := Unit) hd.head
      (matrixInput.weights A₀.Z) (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt A₀.Z hd.places))
    have e' : (baseRows A₀.Z hd.places).map (·.place) = _ := e
    have hm : r.place ∈ (baseRows A₀.Z hd.places).map (·.place) := List.mem_map.2 ⟨r, h1, rfl⟩
    rw [e'] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    show r.place.kind = _ ∨ r.place.kind = _ ∨ r.place.kind = _
    rcases hm with e1 | e1 | e1 | e1 | e1 | e1 <;> rw [e1] <;> simp [ProofFile.Honest.K14.place,
      ProofFile.Honest.K14.sendPlace]
  · exact .inr (.inr (rest_k12 A₀.Z A₀.G r h1))

section
variable (hd : HeadAtReturn files A₀) (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)

/-- At `theG`. -/
theorem k10_rows_at (h₃ : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ L ∈ (theG hd T K).first, L.place.kind = KindName.K10 →
      L.bare ∈ (closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).rows A₀.Z A₀.G := by
  intro L hL hk
  obtain ⟨M, hM, hr, hh⟩ := first_row_of hd T K L hL
  have e := lots_k10 A₀.Z A₀.G M hM _ hh hk
  subst e
  have ef : (K.lots.find? fun s => s.name ==
      (closeLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).name) =
      some (closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :=
    OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) K.lots K.apart _ h₃
  have eo : overlayLot K.lots (closeLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) =
      closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref := by
    unfold overlayLot
    rw [ef]
  rw [eo] at hr
  exact hr

theorem k12_rows_at (h₄ : ProofFile.Honest.K12.Sim2.simulatorLot (X := Unit) matrixInput
    OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ L ∈ (theG hd T K).first, L.place.kind = KindName.K12 →
      L.bare ∈ ProofFile.Honest.K12.Sim2.rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref A₀.Z A₀.G := by
  intro L hL hk
  obtain ⟨M, hM, hr, hh⟩ := first_row_of hd T K L hL
  have e := lots_k12 A₀.Z A₀.G M hM _ hh hk
  subst e
  have ef : (K.lots.find? fun s => s.name ==
      (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).name) =
      some (ProofFile.Honest.K12.Sim2.simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :=
    OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) K.lots K.apart _ h₄
  have eo : overlayLot K.lots (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) =
      ProofFile.Honest.K12.Sim2.simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref := by
    unfold overlayLot
    rw [ef]
  rw [eo] at hr
  exact hr

theorem k10_none_shared_at : ∀ L ∈ (theG hd T K).shared, L.place.kind ≠ KindName.K10 := by
  intro L hL hk
  have h1 := (shared_row_of hd T K L hL).2
  have h2 : L.bare.half.place.kind = KindName.K10 := hk
  rcases shared_kinds hd _ h1 with e | e | e <;> (rw [h2] at e; cases e)

theorem k10_none_second_at : ∀ L ∈ (theG hd T K).second, L.place.kind ≠ KindName.K10 := by
  intro L hL hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  have e : r.place.kind = KindName.K12 := second_of_K K r hr
  have e' : r.place.kind = KindName.K10 := hk
  rw [e'] at e
  cases e

theorem k14_rows_at (hsix : ∀ r ∈ baseRows A₀.Z hd.places, r ∈ K.shared) :
    ∀ L ∈ (theG hd T K).shared, L.place.kind = KindName.K14 → L.bare ∈ baseRows A₀.Z hd.places := by
  intro L hL hk
  exact rows_of_K hd K hsix KindName.K14 (by decide) _ (shared_row_of hd T K L hL).1 hk

theorem k14_none_first_at : ∀ L ∈ (theG hd T K).first, L.place.kind ≠ KindName.K14 := by
  intro L hL hk
  obtain ⟨M, hM, -, hh⟩ := first_row_of hd T K L hL
  exact lots_k14 A₀.Z A₀.G M hM _ hh hk

theorem k14_none_second_at : ∀ L ∈ (theG hd T K).second, L.place.kind ≠ KindName.K14 := by
  intro L hL hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  have e : r.place.kind = KindName.K12 := second_of_K K r hr
  have e' : r.place.kind = KindName.K14 := hk
  rw [e'] at e
  cases e

variable (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)

/-- **At `theGOfReturn`.** -/
theorem k10_rows_theG (h₃ : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ L ∈ (theGOfReturn made hd T K).first, L.place.kind = KindName.K10 →
      L.bare ∈ (closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).rows A₀.Z A₀.G :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.first, L.place.kind = KindName.K10 →
      L.bare ∈ (closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).rows A₀.Z A₀.G) _
    (k10_rows_at hd T K h₃)

/-- **The test at L: a list of the first chain of the kind K12 is a row of `simulatorLot`.** -/
theorem k12_rows_theG (h₄ : ProofFile.Honest.K12.Sim2.simulatorLot (X := Unit) matrixInput
    OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    ∀ L ∈ (theGOfReturn made hd T K).first, L.place.kind = KindName.K12 →
      L.bare ∈ ProofFile.Honest.K12.Sim2.rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref A₀.Z A₀.G :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.first, L.place.kind = KindName.K12 →
      L.bare ∈ ProofFile.Honest.K12.Sim2.rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref A₀.Z A₀.G) _
    (k12_rows_at hd T K h₄)

theorem k10_none_shared : ∀ L ∈ (theGOfReturn made hd T K).shared, L.place.kind ≠ KindName.K10 :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.shared, L.place.kind ≠ KindName.K10) _
    (k10_none_shared_at hd T K)

theorem k10_none_second : ∀ L ∈ (theGOfReturn made hd T K).second, L.place.kind ≠ KindName.K10 :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.second, L.place.kind ≠ KindName.K10) _
    (k10_none_second_at hd T K)

theorem k14_rows_theG (hsix : ∀ r ∈ baseRows A₀.Z hd.places, r ∈ K.shared) :
    ∀ L ∈ (theGOfReturn made hd T K).shared, L.place.kind = KindName.K14 →
      L.bare ∈ baseRows A₀.Z hd.places :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.shared, L.place.kind = KindName.K14 →
      L.bare ∈ baseRows A₀.Z hd.places) _ (k14_rows_at hd T K hsix)

theorem k14_none_first : ∀ L ∈ (theGOfReturn made hd T K).first, L.place.kind ≠ KindName.K14 :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.first, L.place.kind ≠ KindName.K14) _
    (k14_none_first_at hd T K)

theorem k14_none_second : ∀ L ∈ (theGOfReturn made hd T K).second, L.place.kind ≠ KindName.K14 :=
  castSides_of (Q := fun _ G => ∀ L ∈ G.second, L.place.kind ≠ KindName.K14) _
    (k14_none_second_at hd T K)

end

end AtFullSide.M1

#print axioms AtFullSide.M1.k10_rows_theG
#print axioms AtFullSide.M1.k12_rows_theG
#print axioms AtFullSide.M1.k10_none_shared
#print axioms AtFullSide.M1.k10_none_second
#print axioms AtFullSide.M1.k14_rows_theG
#print axioms AtFullSide.M1.k14_none_first
#print axioms AtFullSide.M1.k14_none_second
