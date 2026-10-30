-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RoundsHoldPlaces.lean: "every written round is below, with the radii pinned"
(`RoundsHoldAt`, RoundsHold.lean) at eight closed places of a proximity test (the kind K12): the
four tests of a proof file at the two stored sizes; with tests that can fail.

It stands beside RoundsAtPlaces.lean, which has at the same eight places
another form (`RoundsBelow`) and the bare comparison on "BAT"'s count
(`piU_bat` and its like).
Main names, at `piU`; the like at `piO`, `piW`, `piL`, `piUFull`, `piOFull`, `piWFull`, `piLFull`:
  `payPub_of`, `manyRows`: tools.
  `piU_batPlace`: the test on "BAT" at the place itself (`batPlaceB`) says yes at the closed radii.
    `roundsHold_piU`: `RoundsHoldAt` there: no premise. `roundsBelowAt_piU`: so the form
    `RoundsBelowAt`.
  `piU_pay`, `payPub_piU`: what the payer of "BAT" asks that is public.
  Lines that can fail, each by the kernel: `piU_no_price`: at every radius one more, the test on the
    prices `smallOkB` says no. `piU_yes_less`: at every radius one less it says yes. `piU_no_joh`,
    `piU_no_bat`: at the distances for radii `johOk` and `batPlaceB` say no. `piU_blind`: a warning,
    not a price: there the bare comparison `batPriceOk` says yes. `piU_no_rows`: at 2^70 times the
    rows `batPlaceB` says no. `piU_no_zero`, `piU_no_zero_price`: at the radius 0 `johOk` and
    `smallOkB` say no.
What these lines say together: the closed radii lie in a window. From above the prices bind: one
more at every stage, and `smallOkB` says no, while `johOk` and `batPlaceB` still say yes there (by
evaluation). From below the prices at one less do not refuse, nor does `batPlaceB` at the radius 0
(that one by evaluation); at 0 `johOk` and the prices of the rounds of positions do. So the tests do
not single the closed radii out: that these are the planner's is shown elsewhere
(Sizes/PlacesAtScope.lean).
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: the closed places were made by a program off a run's print; StretchFull.lean holds the
declared rounds of three of them against written lists. The lines that can fail are on tests with
code beside the form; RoundsNot.lean refutes the form itself at a first radius that is not inside
the Johnson bound. One round's share each, no sum; part of the 128 bits is work at "CS" and "BASE";
"BAT"'s number is priced and is no law's count. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.RoundsAtPlaces
import Johnson.Desc.K12.Law.RoundsHold

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member (piU piO piW piL codesSmall rU rO rW rL piUFull piOFull piWFull piLFull codesFull
  rUFull rOFull rWFull rLFull)
open Iop
open scoped ENNReal

/-- What the payer of "BAT" asks that is public (`PayPub`, PayPub.lean), and the comparison on its
count `batV0`, from the condition and the test `batPayOk` (BatPriceOk.lean). -/
theorem payPub_of {p : P12} {r : Fmt.M1.Stage → ℕ} {K : Codes}
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p K ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hb : batPayOk p r 128 = true) :
    ∃ (w0 : WR) (l : List WR), writtenOf p.nums = some (w0 :: l) ∧
      PayPub p (fun s => r s.st) w0.entry.rows (batV0 p r) ∧
      RoundBelow (batV0 p r) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a, rest, w0, l, _, e1, e2, _⟩ := hK.gives
  exact ⟨w0, l, e2, batPay_gives p r (fun s => r s.st) (fun _ => rfl) 128 a rest e1 w0 l e2 hb⟩

/-- The place with 2 ^ 70 times its rows: for a test that must say no. -/
def manyRows (p : P12) : P12 := { p with nums := { p.nums with rows := p.nums.rows * 2 ^ 70 } }

/-! ## piU -/

theorem piU_batPlace : batPlaceB piU (fun s => rU s.st) = true := by decide +kernel

theorem roundsHold_piU : RoundsHoldAt piU (fun s => rU s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piU_r piU_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piU : RoundsBelowAt piU (fun s => rU s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piU.below

theorem piU_pay : batPayOk piU rU 128 = true := by decide +kernel

theorem payPub_piU : ∃ (w0 : WR) (l : List WR), writtenOf piU.nums = some (w0 :: l) ∧
    PayPub piU (fun s => rU s.st) w0.entry.rows (batV0 piU rU) ∧
    RoundBelow (batV0 piU rU) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piU_r piU_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piU_no_price :
    smallOkB (fun s => rU s + 1) (brAt fun s => rU s + 1) piU = false := by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piU_yes_less :
    smallOkB (fun s => rU s - 1) (brAt fun s => rU s - 1) piU = true := by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piU_no_joh : johOk piU (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piU_no_bat : batPlaceB piU (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piU_blind : batPriceOk piU (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piU_no_rows : batPlaceB (manyRows piU) (fun s => rU s.st) = false := by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piU_no_zero : johOk piU (fun _ => 0) = false := by decide +kernel

theorem piU_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piU = false := by
  decide +kernel

/-! ## piO -/

theorem piO_batPlace : batPlaceB piO (fun s => rO s.st) = true := by decide +kernel

theorem roundsHold_piO : RoundsHoldAt piO (fun s => rO s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piO_r piO_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piO : RoundsBelowAt piO (fun s => rO s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piO.below

theorem piO_pay : batPayOk piO rO 128 = true := by decide +kernel

theorem payPub_piO : ∃ (w0 : WR) (l : List WR), writtenOf piO.nums = some (w0 :: l) ∧
    PayPub piO (fun s => rO s.st) w0.entry.rows (batV0 piO rO) ∧
    RoundBelow (batV0 piO rO) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piO_r piO_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piO_no_price :
    smallOkB (fun s => rO s + 1) (brAt fun s => rO s + 1) piO = false := by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piO_yes_less :
    smallOkB (fun s => rO s - 1) (brAt fun s => rO s - 1) piO = true := by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piO_no_joh : johOk piO (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piO_no_bat : batPlaceB piO (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piO_blind : batPriceOk piO (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piO_no_rows : batPlaceB (manyRows piO) (fun s => rO s.st) = false := by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piO_no_zero : johOk piO (fun _ => 0) = false := by decide +kernel

theorem piO_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piO = false := by
  decide +kernel

/-! ## piW -/

theorem piW_batPlace : batPlaceB piW (fun s => rW s.st) = true := by decide +kernel

theorem roundsHold_piW : RoundsHoldAt piW (fun s => rW s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piW_r piW_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piW : RoundsBelowAt piW (fun s => rW s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piW.below

theorem piW_pay : batPayOk piW rW 128 = true := by decide +kernel

theorem payPub_piW : ∃ (w0 : WR) (l : List WR), writtenOf piW.nums = some (w0 :: l) ∧
    PayPub piW (fun s => rW s.st) w0.entry.rows (batV0 piW rW) ∧
    RoundBelow (batV0 piW rW) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piW_r piW_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piW_no_price :
    smallOkB (fun s => rW s + 1) (brAt fun s => rW s + 1) piW = false := by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piW_yes_less :
    smallOkB (fun s => rW s - 1) (brAt fun s => rW s - 1) piW = true := by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piW_no_joh : johOk piW (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piW_no_bat : batPlaceB piW (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piW_blind : batPriceOk piW (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piW_no_rows : batPlaceB (manyRows piW) (fun s => rW s.st) = false := by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piW_no_zero : johOk piW (fun _ => 0) = false := by decide +kernel

theorem piW_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piW = false := by
  decide +kernel

/-! ## piL -/

theorem piL_batPlace : batPlaceB piL (fun s => rL s.st) = true := by decide +kernel

theorem roundsHold_piL : RoundsHoldAt piL (fun s => rL s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piL_r piL_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piL : RoundsBelowAt piL (fun s => rL s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piL.below

theorem piL_pay : batPayOk piL rL 128 = true := by decide +kernel

theorem payPub_piL : ∃ (w0 : WR) (l : List WR), writtenOf piL.nums = some (w0 :: l) ∧
    PayPub piL (fun s => rL s.st) w0.entry.rows (batV0 piL rL) ∧
    RoundBelow (batV0 piL rL) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piL_r piL_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piL_no_price :
    smallOkB (fun s => rL s + 1) (brAt fun s => rL s + 1) piL = false := by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piL_yes_less :
    smallOkB (fun s => rL s - 1) (brAt fun s => rL s - 1) piL = true := by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piL_no_joh : johOk piL (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piL_no_bat : batPlaceB piL (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piL_blind : batPriceOk piL (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piL_no_rows : batPlaceB (manyRows piL) (fun s => rL s.st) = false := by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piL_no_zero : johOk piL (fun _ => 0) = false := by decide +kernel

theorem piL_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piL = false := by
  decide +kernel

/-! ## piUFull -/

theorem piUFull_batPlace : batPlaceB piUFull (fun s => rUFull s.st) = true := by decide +kernel

theorem roundsHold_piUFull : RoundsHoldAt piUFull (fun s => rUFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piUFull_r piUFull_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piUFull : RoundsBelowAt piUFull (fun s => rUFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piUFull.below

theorem piUFull_pay : batPayOk piUFull rUFull 128 = true := by decide +kernel

theorem payPub_piUFull : ∃ (w0 : WR) (l : List WR), writtenOf piUFull.nums = some (w0 :: l) ∧
    PayPub piUFull (fun s => rUFull s.st) w0.entry.rows (batV0 piUFull rUFull) ∧
    RoundBelow (batV0 piUFull rUFull) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piUFull_r piUFull_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piUFull_no_price :
    smallOkB (fun s => rUFull s + 1) (brAt fun s => rUFull s + 1) piUFull = false :=
        by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piUFull_yes_less :
    smallOkB (fun s => rUFull s - 1) (brAt fun s => rUFull s - 1) piUFull = true :=
        by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piUFull_no_joh : johOk piUFull (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piUFull_no_bat : batPlaceB piUFull (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piUFull_blind : batPriceOk piUFull (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piUFull_no_rows : batPlaceB (manyRows piUFull) (fun s => rUFull s.st) = false :=
    by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piUFull_no_zero : johOk piUFull (fun _ => 0) = false := by decide +kernel

theorem piUFull_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piUFull = false := by
  decide +kernel

/-! ## piOFull -/

theorem piOFull_batPlace : batPlaceB piOFull (fun s => rOFull s.st) = true := by decide +kernel

theorem roundsHold_piOFull : RoundsHoldAt piOFull (fun s => rOFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piOFull_r piOFull_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piOFull : RoundsBelowAt piOFull (fun s => rOFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piOFull.below

theorem piOFull_pay : batPayOk piOFull rOFull 128 = true := by decide +kernel

theorem payPub_piOFull : ∃ (w0 : WR) (l : List WR), writtenOf piOFull.nums = some (w0 :: l) ∧
    PayPub piOFull (fun s => rOFull s.st) w0.entry.rows (batV0 piOFull rOFull) ∧
    RoundBelow (batV0 piOFull rOFull) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piOFull_r piOFull_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piOFull_no_price :
    smallOkB (fun s => rOFull s + 1) (brAt fun s => rOFull s + 1) piOFull = false :=
        by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piOFull_yes_less :
    smallOkB (fun s => rOFull s - 1) (brAt fun s => rOFull s - 1) piOFull = true :=
        by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piOFull_no_joh : johOk piOFull (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piOFull_no_bat : batPlaceB piOFull (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piOFull_blind : batPriceOk piOFull (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piOFull_no_rows : batPlaceB (manyRows piOFull) (fun s => rOFull s.st) = false :=
    by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piOFull_no_zero : johOk piOFull (fun _ => 0) = false := by decide +kernel

theorem piOFull_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piOFull = false := by
  decide +kernel

/-! ## piWFull -/

theorem piWFull_batPlace : batPlaceB piWFull (fun s => rWFull s.st) = true := by decide +kernel

theorem roundsHold_piWFull : RoundsHoldAt piWFull (fun s => rWFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piWFull_r piWFull_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piWFull : RoundsBelowAt piWFull (fun s => rWFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piWFull.below

theorem piWFull_pay : batPayOk piWFull rWFull 128 = true := by decide +kernel

theorem payPub_piWFull : ∃ (w0 : WR) (l : List WR), writtenOf piWFull.nums = some (w0 :: l) ∧
    PayPub piWFull (fun s => rWFull s.st) w0.entry.rows (batV0 piWFull rWFull) ∧
    RoundBelow (batV0 piWFull rWFull) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piWFull_r piWFull_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piWFull_no_price :
    smallOkB (fun s => rWFull s + 1) (brAt fun s => rWFull s + 1) piWFull = false :=
        by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piWFull_yes_less :
    smallOkB (fun s => rWFull s - 1) (brAt fun s => rWFull s - 1) piWFull = true :=
        by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piWFull_no_joh : johOk piWFull (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piWFull_no_bat : batPlaceB piWFull (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piWFull_blind : batPriceOk piWFull (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piWFull_no_rows : batPlaceB (manyRows piWFull) (fun s => rWFull s.st) = false :=
    by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piWFull_no_zero : johOk piWFull (fun _ => 0) = false := by decide +kernel

theorem piWFull_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piWFull = false := by
  decide +kernel

/-! ## piLFull -/

theorem piLFull_batPlace : batPlaceB piLFull (fun s => rLFull s.st) = true := by decide +kernel

theorem roundsHold_piLFull : RoundsHoldAt piLFull (fun s => rLFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHoldAt_ofB k12Condition_piLFull_r piLFull_batPlace

/-- The form `RoundsBelowAt`, by `RoundsHoldAt.below`. -/
theorem roundsBelowAt_piLFull : RoundsBelowAt piLFull (fun s => rLFull s.st) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsHold_piLFull.below

theorem piLFull_pay : batPayOk piLFull rLFull 128 = true := by decide +kernel

theorem payPub_piLFull : ∃ (w0 : WR) (l : List WR), writtenOf piLFull.nums = some (w0 :: l) ∧
    PayPub piLFull (fun s => rLFull s.st) w0.entry.rows (batV0 piLFull rLFull) ∧
    RoundBelow (batV0 piLFull rLFull) w0.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  payPub_of k12Condition_piLFull_r piLFull_pay

/-- At every radius one more, the test on the prices says no. -/
theorem piLFull_no_price :
    smallOkB (fun s => rLFull s + 1) (brAt fun s => rLFull s + 1) piLFull = false :=
        by decide +kernel

/-- At every radius one less it says yes: the prices do not pin the radii from below. -/
theorem piLFull_yes_less :
    smallOkB (fun s => rLFull s - 1) (brAt fun s => rLFull s - 1) piLFull = true :=
        by decide +kernel

/-- At the distances for radii the test on the radii says no. -/
theorem piLFull_no_joh : johOk piLFull (fun s => dB s) = false := by decide +kernel

/-- At the distances for radii the test on "BAT" at the place says no. -/
theorem piLFull_no_bat : batPlaceB piLFull (fun s => s.d) = false := by decide +kernel

/-- A warning, not a price: at the distances for radii the Johnson bound's list is cut off to 0, and
the bare comparison on "BAT"'s count says yes. That is why `RoundsHoldAt` holds the first stage's
list as a clause of its own. -/
theorem piLFull_blind : batPriceOk piLFull (fun s => dB s) 128 = true := by decide +kernel

/-- At 2 ^ 70 times the rows the test on "BAT" says no. -/
theorem piLFull_no_rows : batPlaceB (manyRows piLFull) (fun s => rLFull s.st) = false :=
    by decide +kernel

/-- At the radius 0 at every stage the test on the radii says no (its clause "0 < e"), and so does
the test on the prices (the rounds of positions). -/
theorem piLFull_no_zero : johOk piLFull (fun _ => 0) = false := by decide +kernel

theorem piLFull_no_zero_price : smallOkB (fun _ => 0) (brAt fun _ => 0) piLFull = false := by
  decide +kernel

end H2K.Pub

#print axioms H2K.Pub.payPub_of
#print axioms H2K.Pub.piU_batPlace
#print axioms H2K.Pub.roundsHold_piU
#print axioms H2K.Pub.roundsBelowAt_piU
#print axioms H2K.Pub.piU_pay
#print axioms H2K.Pub.payPub_piU
#print axioms H2K.Pub.piU_no_price
#print axioms H2K.Pub.piU_yes_less
#print axioms H2K.Pub.piU_no_joh
#print axioms H2K.Pub.piU_no_bat
#print axioms H2K.Pub.piU_blind
#print axioms H2K.Pub.piU_no_rows
#print axioms H2K.Pub.piU_no_zero
#print axioms H2K.Pub.piU_no_zero_price
#print axioms H2K.Pub.piO_batPlace
#print axioms H2K.Pub.roundsHold_piO
#print axioms H2K.Pub.roundsBelowAt_piO
#print axioms H2K.Pub.piO_pay
#print axioms H2K.Pub.payPub_piO
#print axioms H2K.Pub.piO_no_price
#print axioms H2K.Pub.piO_yes_less
#print axioms H2K.Pub.piO_no_joh
#print axioms H2K.Pub.piO_no_bat
#print axioms H2K.Pub.piO_blind
#print axioms H2K.Pub.piO_no_rows
#print axioms H2K.Pub.piO_no_zero
#print axioms H2K.Pub.piO_no_zero_price
#print axioms H2K.Pub.piW_batPlace
#print axioms H2K.Pub.roundsHold_piW
#print axioms H2K.Pub.roundsBelowAt_piW
#print axioms H2K.Pub.piW_pay
#print axioms H2K.Pub.payPub_piW
#print axioms H2K.Pub.piW_no_price
#print axioms H2K.Pub.piW_yes_less
#print axioms H2K.Pub.piW_no_joh
#print axioms H2K.Pub.piW_no_bat
#print axioms H2K.Pub.piW_blind
#print axioms H2K.Pub.piW_no_rows
#print axioms H2K.Pub.piW_no_zero
#print axioms H2K.Pub.piW_no_zero_price
#print axioms H2K.Pub.piL_batPlace
#print axioms H2K.Pub.roundsHold_piL
#print axioms H2K.Pub.roundsBelowAt_piL
#print axioms H2K.Pub.piL_pay
#print axioms H2K.Pub.payPub_piL
#print axioms H2K.Pub.piL_no_price
#print axioms H2K.Pub.piL_yes_less
#print axioms H2K.Pub.piL_no_joh
#print axioms H2K.Pub.piL_no_bat
#print axioms H2K.Pub.piL_blind
#print axioms H2K.Pub.piL_no_rows
#print axioms H2K.Pub.piL_no_zero
#print axioms H2K.Pub.piL_no_zero_price
#print axioms H2K.Pub.piUFull_batPlace
#print axioms H2K.Pub.roundsHold_piUFull
#print axioms H2K.Pub.roundsBelowAt_piUFull
#print axioms H2K.Pub.piUFull_pay
#print axioms H2K.Pub.payPub_piUFull
#print axioms H2K.Pub.piUFull_no_price
#print axioms H2K.Pub.piUFull_yes_less
#print axioms H2K.Pub.piUFull_no_joh
#print axioms H2K.Pub.piUFull_no_bat
#print axioms H2K.Pub.piUFull_blind
#print axioms H2K.Pub.piUFull_no_rows
#print axioms H2K.Pub.piUFull_no_zero
#print axioms H2K.Pub.piUFull_no_zero_price
#print axioms H2K.Pub.piOFull_batPlace
#print axioms H2K.Pub.roundsHold_piOFull
#print axioms H2K.Pub.roundsBelowAt_piOFull
#print axioms H2K.Pub.piOFull_pay
#print axioms H2K.Pub.payPub_piOFull
#print axioms H2K.Pub.piOFull_no_price
#print axioms H2K.Pub.piOFull_yes_less
#print axioms H2K.Pub.piOFull_no_joh
#print axioms H2K.Pub.piOFull_no_bat
#print axioms H2K.Pub.piOFull_blind
#print axioms H2K.Pub.piOFull_no_rows
#print axioms H2K.Pub.piOFull_no_zero
#print axioms H2K.Pub.piOFull_no_zero_price
#print axioms H2K.Pub.piWFull_batPlace
#print axioms H2K.Pub.roundsHold_piWFull
#print axioms H2K.Pub.roundsBelowAt_piWFull
#print axioms H2K.Pub.piWFull_pay
#print axioms H2K.Pub.payPub_piWFull
#print axioms H2K.Pub.piWFull_no_price
#print axioms H2K.Pub.piWFull_yes_less
#print axioms H2K.Pub.piWFull_no_joh
#print axioms H2K.Pub.piWFull_no_bat
#print axioms H2K.Pub.piWFull_blind
#print axioms H2K.Pub.piWFull_no_rows
#print axioms H2K.Pub.piWFull_no_zero
#print axioms H2K.Pub.piWFull_no_zero_price
#print axioms H2K.Pub.piLFull_batPlace
#print axioms H2K.Pub.roundsHold_piLFull
#print axioms H2K.Pub.roundsBelowAt_piLFull
#print axioms H2K.Pub.piLFull_pay
#print axioms H2K.Pub.payPub_piLFull
#print axioms H2K.Pub.piLFull_no_price
#print axioms H2K.Pub.piLFull_yes_less
#print axioms H2K.Pub.piLFull_no_joh
#print axioms H2K.Pub.piLFull_no_bat
#print axioms H2K.Pub.piLFull_blind
#print axioms H2K.Pub.piLFull_no_rows
#print axioms H2K.Pub.piLFull_no_zero
#print axioms H2K.Pub.piLFull_no_zero_price
