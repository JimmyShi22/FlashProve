-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.Law.CondMembersFull
import Johnson.Desc.K12.Law.BatPriceLaw
import Iop.ErrCap
/-
Johnson/Desc/K12/Law/RoundsAtPlaces.lean: every written round of the test, "BAT" included, at the
eight closed places.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member (piU piO piW piL codesSmall rU rO rW rL piUFull piOFull piWFull piLFull codesFull
  rUFull rOFull rWFull rLFull)
open Iop
open scoped ENNReal

/-- **Every written round of a place's test has its count at most εs of its written verifier
messages**: the round "BAT" at the count `batV0 p r`; the rounds behind it at the counts of the
place's chain at the Johnson letters and the radii r. -/
def RoundsBelow (p : P12) (r : Fmt.M1.Stage → ℕ) (εs : ℝ≥0∞) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
    p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c ∧
    c.rds = l.map WR.rd ∧ RoundBelow (batV0 p r) w0.rd εs ∧ Err.Below c.err εs

theorem roundsBelow_of {p : P12} {r : Fmt.M1.Stage → ℕ} {K : Codes}
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p K ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hb : batPriceOk p r 128 = true) : RoundsBelow p r ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, _, _, _, e8, _⟩ := hK.gives
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, batBelow_of_ok p r 128 a rest e1 w0 l e2 hb, e8⟩

/-- **At the cap**: "BAT"'s count times the sampler's number is at most the round's written verifier
messages divided by 2 ^ 128, rounded down; the chain's counts are at most `Err.cap 128`
(Iop/ErrCap.lean), entry by entry. -/
theorem capped_of {p : P12} {r : Fmt.M1.Stage → ℕ} (h : RoundsBelow p r ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c ∧
      batV0 p r * wOf w0.rd ≤ Fintype.card (wRound w0.rd).Chal / 2 ^ 128 ∧
      Err.le c.err (Err.cap 128 c.sh) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, _, e5, e6⟩ := h
  refine ⟨a, rest, w0, l, c, e1, e2, e3, ?_, Err.le_cap_of_below_inv 128 c.err e6⟩
  refine Err.entry_le_cap 128 _ _ ?_
  rw [ENNReal.inv_pow]
  exact e5

/-- The written rounds of a place that have bits of work: name and number. -/
def workRounds (p : P12) : List (String × Nat) :=
  (((writtenOf p.nums).getD []).filter fun w => w.entry.work != 0).map fun w =>
    (w.entry.name, w.entry.work)

theorem piU_bat : batPriceOk piU rU 128 = true := by decide +kernel

theorem piU_works : workRounds piU = [("CS", 28), ("CS", 28), ("BASE", 28)] := by
  decide +kernel

theorem roundsBelow_piU : RoundsBelow piU rU ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piU_r piU_bat

theorem piO_bat : batPriceOk piO rO 128 = true := by decide +kernel

theorem piO_works : workRounds piO = [("CS", 28), ("CS", 28), ("BASE", 28)] := by
  decide +kernel

theorem roundsBelow_piO : RoundsBelow piO rO ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piO_r piO_bat

theorem piW_bat : batPriceOk piW rW 128 = true := by decide +kernel

theorem piW_works : workRounds piW = [("CS", 20), ("CS", 20), ("BASE", 20)] := by
  decide +kernel

theorem roundsBelow_piW : RoundsBelow piW rW ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piW_r piW_bat

theorem piL_bat : batPriceOk piL rL 128 = true := by decide +kernel

theorem piL_works :
    workRounds piL = [("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("BASE", 20)] := by
  decide +kernel

theorem roundsBelow_piL : RoundsBelow piL rL ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piL_r piL_bat

theorem piUFull_bat : batPriceOk piUFull rUFull 128 = true := by decide +kernel

theorem piUFull_works :
    workRounds piUFull = [("CS", 28), ("CS", 28), ("CS", 28), ("CS", 28), ("BASE", 28)] := by
  decide +kernel

theorem roundsBelow_piUFull : RoundsBelow piUFull rUFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piUFull_r piUFull_bat

theorem piOFull_bat : batPriceOk piOFull rOFull 128 = true := by decide +kernel

theorem piOFull_works :
    workRounds piOFull = [("CS", 28), ("CS", 28), ("CS", 28), ("BASE", 28)] := by
  decide +kernel

theorem roundsBelow_piOFull : RoundsBelow piOFull rOFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piOFull_r piOFull_bat

theorem piWFull_bat : batPriceOk piWFull rWFull 128 = true := by decide +kernel

theorem piWFull_works :
    workRounds piWFull = [("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("BASE", 20)] := by
  decide +kernel

theorem roundsBelow_piWFull : RoundsBelow piWFull rWFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piWFull_r piWFull_bat

theorem piLFull_bat : batPriceOk piLFull rLFull 128 = true := by decide +kernel

theorem piLFull_works :
    workRounds piLFull =
    [("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("BASE", 20)] := by
  decide +kernel

theorem roundsBelow_piLFull : RoundsBelow piLFull rLFull ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_of k12Condition_piLFull_r piLFull_bat

end H2K.Pub

#print axioms H2K.Pub.capped_of
#print axioms H2K.Pub.piUFull_works
#print axioms H2K.Pub.piUFull_bat
#print axioms H2K.Pub.roundsBelow_piU
#print axioms H2K.Pub.roundsBelow_piO
#print axioms H2K.Pub.roundsBelow_piW
#print axioms H2K.Pub.roundsBelow_piL
#print axioms H2K.Pub.roundsBelow_piUFull
#print axioms H2K.Pub.roundsBelow_piOFull
#print axioms H2K.Pub.roundsBelow_piWFull
#print axioms H2K.Pub.roundsBelow_piLFull
