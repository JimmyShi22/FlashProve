-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/KindPaysK1AtTheG.lean: the shared "sending" (the kind K1): **KindPays G .K1 AT THE NAMED SIDES**: G := theGOfReturn made h T K
(E2E/TheG.lean: the sides at a return of the maker: the letters are the three chains' threads, the rows those that the kinds
lay over the filling's own halves, the falls the lists at the term), AT THE BASE FILLING, in scope, where the gate accepts. The
three premises of kindPays_K1_of_rows (KindPaysK1.lean) are PAID here from ONE premise on what the kinds lay:

  K1Laid h K        of the kinds' rows K: under the name of the filling's first lot K lays lotS, under the name of its last lot wS
                    (our two lots, at the base's letters); at the places of the shared chain's two sendings K lays
                    sendingRows (simPub A.Z h.places) at the base filling's own weights and randomness. Three equations of
                    "find?": a choice of whoever lays K
  rows₁_at_theG     each list of (theG h T K).first at a place of the kind K1 bears one of our 52 rows: the other lots' rows,
                    a kind's own or bare, keep their halves' places, and none of these is of the kind K1
  rows₂_at_theG     each list of its shared chain at a place of the kind K1 bears one of the two sendings' rows: the base
                    filling's shared halves are the six rows' halves and the two tests' pairs
  none₃_at_theG     NO LIST OF ITS LAST CHAIN STANDS AT A PLACE OF THE KIND K1: the base filling lays the request's own test there
                    alone (placeW, of the kind K12)
  **kindPays_K1_at_theG**   KindPays (theGOfReturn made h T K) .K1

Limits. K1Laid is a premise: no value of K is laid here. All limits of KindPaysK1.lean: Good at predicates that never hold; clause
is another house's law, called. The base filling alone: the filling that the online prover reads is reached by the crossing.
It stands over E2E/TheSides.lean and E2E/TheG.lean at another house's newest lot. No property of the protocol is claimed.
-/
import AtFullSide.K1.KindPaysK1
import E2E.TheG
import AtFullSide.K12.ReturnsAtFillW
import Johnson.Desc.ProofFile.Honest.K14.Sim.AtFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open VerifiableInference.Compilation (KindPays)
open OnBytes (TableKey)
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim ProofFile.Honest.Term
open ProofFile.Honest.K14 (sendingRows simRows ownRows simPub simData randNow simRows_now ownRows_four
  sendings_at_head)
open ProofFile.Honest.K12.AtProof (sharedWithUO halfU halfO halfW placeU placeO placeW)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- Our first lot at the base's letters. -/
abbrev baseLotS : SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  lotS matrixInput id id OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref

/-- Our last lot at the base's letters. -/
abbrev baseWS : SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  wS matrixInput id id OnBytes.secondHashFunction openHonest

/-- The shared chain's two sendings' rows at the base filling's own weights and randomness. -/
abbrev baseSendings (h : HeadAtReturn files A) :
    List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) :=
  sendingRows (simPub A.Z h.places) (matrixInput.weights A.Z)
    (randNow (VerifiableInference.Desc.K1.qAt A.Z h.places))

/-- **What is asked of the kinds' rows.** -/
structure K1Laid (h : HeadAtReturn files A) (K : KindRows (baseFilling files) A.Z A.G) : Prop where
  lot : (K.lots.find? fun s => s.name == baseLotS.toHLot.name) = some baseLotS
  w : (K.lots.find? fun s => s.name == baseWS.toHLot.name) = some baseWS
  shared : ∀ r ∈ baseSendings h, (K.shared.find? fun x => x.place == r.half.place) = some r

/-- A row of the overlay stands at its side's place. -/
theorem overlayRow_place {V W Y Pb : Type} (mine : List (Unlettered V W Y Pb)) (x : Placed V W Y) :
    (overlayRow mine x).place = x.place := by
  unfold overlayRow
  cases e : mine.find? fun r => r.place == x.place with
  | some r =>
    have hp := List.find?_some e
    exact beq_iff_eq.1 hp
  | none => rfl

/-- **Each list of the first chain at a place of the kind K1 bears one of our 52 rows.** -/
theorem rows₁_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) (hK : K1Laid h K) :
    ∀ L ∈ (theG h T K).first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [baseLotS, baseWS],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud := by
  intro L hL hk
  have hL' : L ∈ (rowsOfLots A.Z A.G ((baseFilling files).lots.map (overlayLot K.lots))).map
      (theLetters h T).first := hL
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL'
  have hk' : r.place.kind = .K1 := hk
  unfold rowsOfLots at hr
  obtain ⟨s, hs, hrs⟩ := List.mem_flatMap.1 hr
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hs
  have hM₀ := hM
  rw [show (baseFilling files).lots = _ from
    lots_split_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest] at hM
  rcases List.mem_cons.1 hM with rfl | hM
  · have e : overlayLot K.lots baseLotS.toHLot = baseLotS := by
      unfold overlayLot
      rw [hK.lot]
    rw [e] at hrs
    exact ⟨r, List.mem_flatMap.2 ⟨_, List.mem_cons_self, hrs⟩, rfl, rfl, rfl, rfl⟩
  · rcases List.mem_append.1 hM with hM | hM
    · exfalso
      have hh : ((overlayLot K.lots M).rows A.Z A.G).map (·.half) = M.halves A.Z A.G :=
        overlay_half (K.lots_fit M hM₀)
      have hm : r.half ∈ M.halves A.Z A.G := hh ▸ List.mem_map_of_mem hrs
      exact others_not_k1_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z
        A.G M hM r.half hm hk'
    · obtain rfl := List.mem_singleton.1 hM
      have e : overlayLot K.lots baseWS.toHLot = baseWS := by
        unfold overlayLot
        rw [hK.w]
      rw [e] at hrs
      exact ⟨r, List.mem_flatMap.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hrs⟩, rfl, rfl,
        rfl, rfl⟩

/-- **Each list of the shared chain at a place of the kind K1 bears one of the two sendings' rows.** -/
theorem rows₂_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) (hK : K1Laid h K) :
    ∀ L ∈ (theG h T K).shared, L.place.kind = .K1 →
      ∃ r ∈ baseSendings h, L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud := by
  intro L hL hk
  have hL' : L ∈ (((baseFilling files).shared A.Z A.G).map (overlayRow K.shared)).map
      (theLetters h T).shared := hL
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hL'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have hk' : y.place.kind = .K1 := by
    rw [← overlayRow_place K.shared y]
    exact hk
  have hs := simRows_now (Pb := TableKey) h.head (matrixInput.weights A.Z)
  have hy' : y ∈ sharedWithUO matrixInput A.Z := hy
  unfold sharedWithUO at hy'
  rw [hs] at hy'
  rcases List.mem_append.1 hy' with hy' | hy'
  · rcases List.mem_append.1 hy' with hy' | hy'
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy'
      rcases List.mem_append.1 (show r ∈ ownRows (simData A.Z h.places) (matrixInput.weights A.Z) ++
        baseSendings h from hr) with hr | hr
      · exfalso
        have hp := List.mem_map_of_mem (f := (·.place)) hr
        rw [ownRows_four _ _ (sendings_at_head h.head).2.1] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        have hk2 : r.place.kind = .K1 := hk'
        rcases hp with e | e | e | e <;> · rw [e] at hk2; cases hk2
      · have e : overlayRow K.shared r.half = r := by
          unfold overlayRow
          rw [hK.shared r hr]
        rw [e]
        exact ⟨r, hr, rfl, rfl, rfl, rfl⟩
    · exfalso
      rw [AtFullSide.K12.halfU_place _ _ _ y hy'] at hk'
      cases hk'
  · exfalso
    rw [AtFullSide.K12.halfO_place _ _ y hy'] at hk'
    cases hk'

/-- **No list of the last chain stands at a place of the kind K1.** -/
theorem none₃_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) :
    ∀ L ∈ (theG h T K).second, L.place.kind ≠ .K1 := by
  intro L hL hk
  have hL' : L ∈ (((baseFilling files).second A.Z A.G).map (overlayRow K.second)).map
      (theLetters h T).second := hL
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hL'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have hk' : y.place.kind = .K1 := by
    rw [← overlayRow_place K.second y]
    exact hk
  have hy' : y ∈ secondW matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G := hy
  unfold secondW at hy'
  split at hy'
  · rw [AtFullSide.K12.halfW_place _ _ _ _ _ _ _ _ _ _ y hy'] at hk'
    cases hk'
  · cases hy'

/-- **KindPays AT THE NAMED SIDES.** -/
theorem kindPays_K1_at_theG (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK : K1Laid h K) : KindPays (theGOfReturn made h T K) .K1 := by
  refine kindPays_K1_of_rows hS hL matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest made h _
    (matrixInput.weights A.Z) (randNow (VerifiableInference.Desc.K1.qAt A.Z h.places)) ?_ ?_ ?_
  · exact castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [baseLotS, baseWS],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) _ (rows₁_at_theG h T K hK)
  · exact castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.shared, L.place.kind = .K1 →
      ∃ r ∈ baseSendings h, L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) _
      (rows₂_at_theG h T K hK)
  · exact castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.second, L.place.kind ≠ .K1) _
      (none₃_at_theG h T K)

end AtFullSide.K1

#print axioms AtFullSide.K1.overlayRow_place
#print axioms AtFullSide.K1.rows₁_at_theG
#print axioms AtFullSide.K1.rows₂_at_theG
#print axioms AtFullSide.K1.none₃_at_theG
#print axioms AtFullSide.K1.kindPays_K1_at_theG
