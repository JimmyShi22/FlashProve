-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Sim/HalvesAtReturn.lean: the shared "sending" (the kind K1): THE TIE OF
OUR ROWS TO THE MAKER's PROVER, AS EQUATIONS OF LISTS IN THE FILLING's ORDER. At what onlineProverFromPublicFiles returns at
the base filling onlineProverPartsInUse I o S O, and at that filling read through, the first chain's prover's
sides are: our first lot's rows' halves, then the other lots' halves, then our last lot's; and the sides
at places of the kind K1, in order, ARE our 52 rows' halves. Five theorems; no definition.

  filter_three      a list a ++ m ++ b, a and b at places of the kind K1, m at none: filtered by that
                    kind it is a ++ b
  our_kind          every row of the two values stands at a place of the kind K1
  first_at_base, first_at_through   A.H.first, in three stretches
  k1_halves_at_base, k1_halves_at_through   THE SIDES OF THE KIND K1 ARE OUR ROWS' HALVES

By what. atPure_ok (Honest/AtPureLaw.lean); lots_split, lots_split_base, others_not_k1,
others_not_k1_base (AtFill.lean); FirstFill.k1_kind (Honest/Thread/FirstFillKinds.lean); w_of_job
(Johnson/SendSim/Seat/AtDescStands.lean).

Limits. The first chain alone. Equations of definitions: they say nothing of what a side plays. No
property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K1.Sim.AtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1.Sim
open VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

variable {W₀ W₀' Rc' : Type}

/-- Filtered by the kind K1, a ++ m ++ b is a ++ b. -/
theorem filter_three {V W X : Type} {a m b : List (Placed V W X)}
    (ha : ∀ x ∈ a, x.place.kind = .K1) (hm : ∀ x ∈ m, x.place.kind ≠ .K1)
    (hb : ∀ x ∈ b, x.place.kind = .K1) :
    ((a ++ m ++ b).filter fun x => x.place.kind == .K1) = a ++ b := by
  rw [List.filter_append, List.filter_append,
    List.filter_eq_self.2 fun x hx => beq_iff_eq.2 (ha x hx),
    List.filter_eq_self.2 fun x hx => beq_iff_eq.2 (hb x hx),
    List.filter_eq_nil_iff.2 fun x hx h => hm x hx (beq_iff_eq.1 h), List.append_nil]

/-- **Every row of the two values stands at a place of the kind K1.** -/
theorem our_kind (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zp : Pub) (G : Ground) :
    (∀ x ∈ (lotS I g rd o S).toHLot.halves Zp G, x.place.kind = .K1) ∧
      ∀ x ∈ (wS I g rd o O).toHLot.halves Zp G, x.place.kind = .K1 := by
  constructor
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (show x ∈ List.map Unlettered.half
      ((lotJobs (lotNo o Zp) (lotData S) Zp G).map (jobRow (witAt I g rd Zp))) from hx)
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
    have hm : placeHalf (V := Unit) (id : PlaceIn Inst → PlaceIn Inst) J ∈
        (dataSideNo (V := Unit) (X := Unit) S (id : PlaceIn Inst → PlaceIn Inst) o).halves Zp G := by
      show _ ∈ lotHalves id (lotNo o Zp) (lotData S) Zp G
      rw [lotHalves_eq]
      exact List.mem_map.2 ⟨J, hJ, rfl⟩
    exact FirstFill.k1_kind S id o Zp G _ hm
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (show x ∈ List.map Unlettered.half
      ((wJobs (lotNo o Zp) (K13.wDataAt O.pile) Zp G).map (jobRow (witAt I g rd Zp))) from hx)
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
    obtain ⟨msg, -, rfl⟩ := w_of_job _ _ Zp G hJ
    rfl

/-- **The first chain's sides at a return at the base filling**, in three stretches. -/
theorem first_at_base {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    A.H.first = (lotS I id id o S).toHLot.halves A.Z A.G ++
      firstOf A.Z A.G ((widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]) ++
      (wS I id id o O).toHLot.halves A.Z A.G := by
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1, lots_split_base]
  unfold firstOf
  rw [List.flatMap_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

/-- **The same at the filling read through.** -/
theorem first_at_through {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A) :
    A.H.first = (lotS I g rd o S).toHLot.halves A.Z A.G ++
      firstOf A.Z A.G (((widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]).map
        (HLot.thru (Local.thru g rd) (Local.thru g rd))) ++
      (wS I g rd o O).toHLot.halves A.Z A.G := by
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1, lots_split]
  unfold firstOf
  rw [List.flatMap_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

/-- **AT A RETURN AT THE BASE FILLING THE SIDES AT PLACES OF THE KIND K1, IN ORDER, ARE OUR ROWS'
HALVES.** -/
theorem k1_halves_at_base {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    (A.H.first.filter fun x => x.place.kind == .K1) =
      (rowsOfLots A.Z A.G [lotS I id id o S, wS I id id o O]).map (·.half) := by
  rw [first_at_base I o S O hA, filter_three (our_kind I id id o S O A.Z A.G).1 ?_
    (our_kind I id id o S O A.Z A.G).2, halves_of_lots]
  · unfold firstOf
    rw [List.map_cons, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  · intro x hx
    obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.1 hx
    exact others_not_k1_base I o S O A.Z A.G M hM x hxM

/-- **The same at the filling read through.** -/
theorem k1_halves_at_through {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A) :
    (A.H.first.filter fun x => x.place.kind == .K1) =
      (rowsOfLots A.Z A.G [lotS I g rd o S, wS I g rd o O]).map (·.half) := by
  rw [first_at_through I g rd d' o S O hA, filter_three (our_kind I g rd o S O A.Z A.G).1 ?_
    (our_kind I g rd o S O A.Z A.G).2, halves_of_lots]
  · unfold firstOf
    rw [List.map_cons, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  · intro x hx
    obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.1 hx
    exact others_not_k1 I g rd o S O A.Z A.G M hM x hxM

end ProofFile.Honest.K1.Sim

#print axioms ProofFile.Honest.K1.Sim.filter_three
#print axioms ProofFile.Honest.K1.Sim.our_kind
#print axioms ProofFile.Honest.K1.Sim.first_at_base
#print axioms ProofFile.Honest.K1.Sim.first_at_through
#print axioms ProofFile.Honest.K1.Sim.k1_halves_at_base
#print axioms ProofFile.Honest.K1.Sim.k1_halves_at_through
