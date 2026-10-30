-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheFallsRoad.lean: THE ROAD TO THE ONE STATEMENT ON THE FALLS. The law that bounds the falls'
measure ends in a sum of prices, member by member, at a letter qF on which it asks five inequalities.
This file lays that letter, proves the inequalities, and brings the sum within the room.

  fallsQ                 the letter: a fall's share at the kit
  fallsQ_share, fallsQ_quiet, fallsQ_coinZero   the inequalities, at the three forms they take
  ps_apart, ps_length    the written places of the first chain are apart; there are 358
  marks_small            the kinds' lines give the test on the marks
  fallsMeasured_room_of_sum   a measure at most that sum is at most the room

Limits. The law itself is a premise here, by its end: plain. This file proves nothing about
completeness, soundness or zero knowledge.
-/
import E2E.TheFallsPrice
import Johnson.Desc.ProofFile.Honest.Law.CoverReps

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.TheFalls
open ProofFile.Honest
open VerifiableInference.Desc (Block Place)

/-- **The letter**: a fall's stated share at the kit. -/
def fallsQ {S Cl : Type} (_ : Block S Cl) (g : Fall S) : ℝ≥0∞ := atKit oneElement g.share

theorem one_le_oneElement : 1 ≤ oneElement :=
  one_le_pow₀ (Iop.one_le_kapSl 128)

/-- A share is at most its price at the kit. -/
theorem fallsQ_share {S Cl : Type} (b : Block S Cl) (g : Fall S) : g.share.val ≤ fallsQ b g := by
  unfold fallsQ atKit Odds.val
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_left' ?_ _
  calc ((g.share.den : ℕ) : ℝ≥0∞)⁻¹ = 1 * ((g.share.den : ℕ) : ℝ≥0∞)⁻¹ := (one_mul _).symm
    _ ≤ oneElement * ((g.share.den : ℕ) : ℝ≥0∞)⁻¹ := mul_le_mul_right' one_le_oneElement _

/-- The bound of K9's fall is its price at the kit. -/
theorem fallsQ_quiet (n top E : ℕ) (ng : Nat → Odds) (hng : ∀ l, ng l = ⟨0, 1⟩) (l : ℕ) :
    Iop.kapSl 128 ^ 3 * ((n * top : ℕ) : ℝ≥0∞) / (E : ℝ≥0∞) ≤
      atKit oneElement ((K9.batFallShare n top E).plus (ng l)) := by
  rw [hng]
  unfold atKit oneElement K9.batFallShare Odds.plus
  simp only [mul_one, zero_mul, add_zero]
  simp only [div_eq_mul_inv]
  apply le_of_eq
  ring

/-- The bound of K4's fall is its price at the kit. -/
theorem fallsQ_coinZero :
    Iop.kapSl 128 ^ 3 * 1 / ((K4.k4CoinZeroShare.den : ℕ) : ℝ≥0∞) ≤
      atKit oneElement K4.k4CoinZeroShare := by
  unfold atKit oneElement
  simp only [div_eq_mul_inv]
  apply le_of_eq
  have : ((K4.k4CoinZeroShare.num : ℕ) : ℝ≥0∞) = 1 := by
    show ((1 : ℕ) : ℝ≥0∞) = 1
    simp
  rw [this]
  ring

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The written places of the first chain are apart. -/
theorem ps_apart : decide P5J.At.ps.Nodup = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- There are 358. -/
theorem ps_length : P5J.At.ps.length = 358 := by decide +kernel

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **The kinds' lines give the test on the marks.** -/
theorem marks_small (h : ShareLines Zp G₀) : (theMarks Zp G₀).all markSmall = true := by
  unfold theMarks
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h.marksK8, h.marksK3⟩, h.marksK4⟩, h.marksK5⟩, h.marksK6⟩

end AtPublicFiles.TheFalls

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain)
open ProofFile.Honest (ProverCoinCounts Sides priceAt repsAt fallsFull)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open P5J
open AtPublicFiles.TheSides AtPublicFiles.TheFalls

local instance (priority := high) theFallsRoadNonemptyPadZ : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) theFallsRoadNonemptyRunValue : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) theFallsRoadInhabitedRunValue : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl)

/-- **A measure at most the sum of prices is at most the room.** -/
theorem fallsMeasured_room_of_sum (hM : onlineMaker Z = .ok returned)
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain xh)
    {pre₁ : List (Block TS ProofFile.Cl)} {e₁ : Block TS ProofFile.Cl}
    (cut : firstChain.blocksInOrder = pre₁ ++ [e₁]) (lines : ShareLines returned.Z returned.G)
    {qM : Block TS ProofFile.Cl → ProofFile.Honest.Mark → ℝ≥0∞} (hq : ∀ b mk, qM b mk ≤ markPrice mk)
    {Relation : FullSizeMatrix → XF → Prop} {G : OnlineSides returned places firstChain}
    (plain : FallsMeasured returned places firstChain G Relation
      ((List.range pre₁.length).map
        (priceAt pre₁ (theMarks returned.Z returned.G) qM
          (repsAt firstChain.blocksInOrder
            (fallsFull returned.Z returned.G noneNotGood (roundsBeforeK4 firstChain))) fallsQ)).sum) :
    FallsMeasured returned places firstChain G Relation fallsRoom := by
  have hps := ProofFile.Honest.places_full h
  have hapart : (firstChain.blocksInOrder.map (·.place)).Nodup := by
    rw [hps]
    exact of_decide_eq_true ps_apart
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  have eG := ground_of_head returned places firstChain hM h O.made
  have l₄ : (theMarks returned.Z returned.G).length = 164 := by
    rw [← eG]
    exact theMarks_164 h O.made
  have l₁ : (fallsFull returned.Z returned.G noneNotGood (roundsBeforeK4 firstChain) :
      List (ProofFile.Honest.Fall TS)).length = 87 := by
    rw [← eG]
    exact ProofFile.Honest.fallsFull_87 h O.made
  refine fallSmall_mono plain (price_le_room firstChain.blocksInOrder pre₁ [e₁] cut _ qM _ fallsQ hapart
    (le_of_eq l₄) (le_of_eq l₁)
    (fun b mk hmk => le_trans (hq b mk)
      (markPrice_le (List.all_eq_true.1 (marks_small lines) mk hmk))) ?_)
  intro b g hg
  exact atKit_le oneElement_le (fallsFull_small lines g hg)

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.TheFalls.fallsQ_share
#print axioms AtPublicFiles.TheFalls.fallsQ_quiet
#print axioms AtPublicFiles.TheFalls.fallsQ_coinZero
#print axioms AtPublicFiles.TheFalls.ps_apart
#print axioms AtPublicFiles.TheFalls.ps_length
#print axioms AtPublicFiles.TheFalls.marks_small
#print axioms AtPublicFiles.AtFiles.HonestTerm.fallsMeasured_room_of_sum
