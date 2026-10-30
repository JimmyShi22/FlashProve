-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/QuietK10K12W.lean: reading a filling through keeps a lot and a half quiet, and the
last chain's proximity test is quiet (the words: Johnson/P1K8R/QuietLots.lean).

  thru_quiet, halfThru_quiet, lotThru_quiet   a part, a half and a lot read through
  through_lots_quiet, through_second_quiet    the lots and the second chain's halves of a filling
                                              read through
  needsField_quiet, halfNeeds_quiet           a part and a half behind the guard on the columns
  halfW_quiet, secondW_quiet                  the last chain's proximity test

Limits. A statement on the second stops and their stated shares alone. A list may be empty: the
statements are then idle there. Nothing is said of what a part sends or whether it plays.
-/
import Johnson.P1K8R.QuietK10K12
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfWAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8.K10K12
open ProofFile ProofFile.Honest

section Thru
variable {V V' W W' X : Type}

/-- A part read through is quiet if the part is. -/
theorem thru_quiet (see : V' → V) (wit : W' → W) {p : Part V W X} (h : Quiet p) :
    Quiet (p.thru see wit) :=
  quiet_lift see wit id (fun _ y => y) h

/-- A half read through is quiet if the half is. -/
theorem halfThru_quiet (see : V' → V) (wit : W' → W) {x : Placed V W X} (h : HalfQuiet x) :
    HalfQuiet (x.thru see wit) := by
  intro p hp
  have hp' : p ∈ x.parts.map (Part.thru see wit) := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
  exact thru_quiet see wit (h q hq)

/-- A lot read through is quiet if the lot is. -/
theorem lotThru_quiet (see : V' → V) (wit : W' → W) {L : HLot V W X} (h : LotQuiet L) :
    LotQuiet (L.thru see wit) := by
  intro Z G x hx
  have hx' : x ∈ (L.halves Z G).map (Placed.thru see wit) := hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
  exact halfThru_quiet see wit (h Z G y hy)

end Thru

section Through
variable {W₀ W₀' Rc Rc' Tr X₀ X : Type}

/-- Every lot of a filling read through is quiet if every lot of the filling is. -/
theorem through_lots_quiet (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    (P : OnlineProverParts W₀ Rc Tr X₀ X) (h : ∀ L ∈ P.lots, LotQuiet L) :
    ∀ L ∈ (OnlineProverParts.through g rd d' P).lots, LotQuiet L := by
  intro L hL
  have hL' : L ∈ P.lots.map (HLot.thru (Local.thru g rd) (Local.thru g rd)) := hL
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hL'
  exact lotThru_quiet _ _ (h M hM)

/-- Every half of the second chain of a filling read through is quiet if every half of the
filling's is. -/
theorem through_second_quiet (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    (P : OnlineProverParts W₀ Rc Tr X₀ X) (h : ∀ Z G, ∀ x ∈ P.second Z G, HalfQuiet x) :
    ∀ Z G, ∀ x ∈ (OnlineProverParts.through g rd d' P).second Z G, HalfQuiet x := by
  intro Z G x hx
  have hx' : x ∈ (P.second Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) := hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
  exact halfThru_quiet _ _ (h Z G y hy)

end Through

section Guard
variable {V W X : Type}

/-- A part behind the guard on the columns is quiet if the part is. -/
theorem needsField_quiet {p : Part V W X} (h : Quiet p) : Quiet p.needsField :=
  ⟨h.1, h.2⟩

/-- A half behind the guard on the columns is quiet if the half is. -/
theorem halfNeeds_quiet {x : Placed V W X} (h : HalfQuiet x) : HalfQuiet x.needsField := by
  intro p hp
  have hp' : p ∈ x.parts.map Part.needsField := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
  exact needsField_quiet (h q hq)

end Guard

section Last
variable {V W₀ Rc Xi Tr X : Type}

/-- The pair at the last chain's proximity test is quiet, at all its letters. -/
theorem halfW_quiet (S : OnBytes.HonestTrace.Sz) (Fd : VerifiableInference.Desc.FileDescription Xi)
    (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : Pub → Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : Pub) (G : Ground) :
    ∀ x ∈ (K12.AtProof.halfW S Fd enter pile no readers weights rand Z G :
      List (Placed V (Local W₀ Rc Xi Tr) X)), HalfQuiet x := by
  intro x hx
  unfold K12.AtProof.halfW at hx
  obtain ⟨J, -, rfl⟩ := List.mem_map.1 hx
  exact halfNeeds_quiet (testHalf_quiet J)

/-- **The last chain's sides are quiet**, at all letters. -/
theorem secondW_quiet (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ x ∈ (secondW I o S O Z G :
      List (Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X)),
      HalfQuiet x := by
  intro x hx
  unfold secondW at hx
  split at hx
  all_goals first
    | exact halfW_quiet _ _ _ _ _ _ _ _ _ _ x hx
    | cases hx

end Last

end P1K8.K10K12

#print axioms P1K8.K10K12.thru_quiet
#print axioms P1K8.K10K12.halfThru_quiet
#print axioms P1K8.K10K12.lotThru_quiet
#print axioms P1K8.K10K12.through_lots_quiet
#print axioms P1K8.K10K12.through_second_quiet
#print axioms P1K8.K10K12.needsField_quiet
#print axioms P1K8.K10K12.halfNeeds_quiet
#print axioms P1K8.K10K12.halfW_quiet
#print axioms P1K8.K10K12.secondW_quiet
