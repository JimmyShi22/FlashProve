-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecCodes.lean: the facts on sizes, radii, rounds and corners that the theorem
`link_chain_joh` (OnBytes/Slice/LinkChainJoh.lean) asks, at the small files of the setting "record
with work".

That theorem asks no fact on codes but the theorem on codes, taken as given (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove). It asks conditions on sizes and radii, on what the
rounds send and draw, and that corners are different. This file supplies them at the sizes `srSz`,
the stages `srSg1` to `srSg3` and the rounds `srRd` (OnBytes/Slice/SmallRecSz.lean), at these radii:
6,137,119 for the stored tables' decoder and both folds; 65,304 for the first stage and for a folded
row's oracle message; 10,490 for the second and the third stage. All four are beyond half the
distance of their code and below its Johnson radius.

Main theorems.
 `srSg1_group` and its like, `sr_positions`   the three stages have the sizes of the planner's three
               groups, and the planner's numbers of positions.
 `srSg1_sized`, `srSg1_pos`, `srSg1_d` and their like   the stages meet `Sg.Sized` and `Sg.Pos`;
               their distances are 98,208, 14,271 and 14,271, each that of the main rows.
 `srSg1_J`, `srSg2_J`, `srSg3_J`, `sr_sg_J`   the stages meet `Sg.StageJ` at the three radii.
 `sr_beyond`   twice each radius is above the distance. `sr_lists`: the Johnson bound's lists there
               are 241, 516 and 516; `sr_list_tables`: that of the tables' code is 114.
 `sr_fit12`, `sr_fit23`, `sr_fit12g`, `sr_rounds12`, `sr_rounds12g`, `sr_rounds23`, `sr_fold1`,
 `sr_fold2`, `sr_lambda`   sizes and rounds at the two folds, the two code switches and the base
               case.
 `sr_batDraws`, `sr_draws`, `sr_bat`   what the first six rounds send and draw.
 `sr_radJ`     the tables' code and its three radii meet `Sz.RadJ`, beyond half the distance.
 `sr_memb`     the code of the two folded rows, and its radius below the Johnson radius.
 `sr_row_pow`, `sr_pl_inj`, `sr_memb_plc_inj`   a row has 2^15 places; corners are different.

Not claimed. That the four radii are the typed parameters' (the planner's distances times the
lengths, rounded down; the planner itself has no radii in whole positions):
OnBytes/Slice/SmallRecRadii.lean [not in this library] holds them against the values typed under
OnBytes/Params/. Nothing on the sizes of error counts but the four lists: `bchksBound` is evaluated
nowhere here. Nothing on a protocol, a decision or a file.

-/
import OnBytes.Slice.BatAt
import OnBytes.Slice.CornersAt
import OnBytes.Slice.CsMet
import OnBytes.Slice.DrawsOKOf
import OnBytes.Slice.GroupFit
import OnBytes.Slice.LinkRecBchks
import OnBytes.Slice.ManyHoldsJoh
import OnBytes.Slice.SmallRecRounds

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Cb.Ood _root_.Run _root_.Run.PQ

/-! ## The three stages -/

/-- The first stage has the sizes of the planner's first group. -/
theorem srSg1_group : srSg1.FitsGroup Params.smallRecordG1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The second stage has the sizes of the planner's second group. -/
theorem srSg2_group : srSg2.FitsGroup Params.smallRecordG2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The third stage has the sizes of the planner's third group. -/
theorem srSg3_group : srSg3.FitsGroup Params.smallRecordG3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The stages' numbers of positions are the planner's. -/
theorem sr_positions : Params.smallRecordStages.map (·.t) = [srSg1.t, srSg2.t, srSg3.t] := rfl

/-- The first stage meets what is asked of a stage's sizes. -/
theorem srSg1_sized : srSg1.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The second stage meets what is asked of a stage's sizes. -/
theorem srSg2_sized : srSg2.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The third stage meets what is asked of a stage's sizes. -/
theorem srSg3_sized : srSg3.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- Each code of the first stage has a coefficient. -/
theorem srSg1_pos : srSg1.Pos := ⟨by decide, by decide⟩

/-- Each code of the second stage has a coefficient. -/
theorem srSg2_pos : srSg2.Pos := ⟨by decide, by decide⟩

/-- Each code of the third stage has a coefficient. -/
theorem srSg3_pos : srSg3.Pos := ⟨by decide, by decide⟩

/-- The distance of the first stage: 2^17 - 32,865 + 1, that of its main rows. -/
theorem srSg1_d : srSg1.d = 98208 := by decide

/-- The distance of the second stage: 2^14 - 2,114 + 1, that of its main rows. -/
theorem srSg2_d : srSg2.d = 14271 := by decide

/-- The distance of the third stage: 2^14 - 2,114 + 1, that of its main rows. -/
theorem srSg3_d : srSg3.d = 14271 := by decide

/-- The first stage at the radius 65,304: sizes in order, two coefficients or more in each code, and
the radius below the stage's Johnson radius. -/
theorem srSg1_J : srSg1.StageJ 65304 where
  sized := srSg1_sized
  pos := srSg1_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The second stage at the radius 10,490. -/
theorem srSg2_J : srSg2.StageJ 10490 where
  sized := srSg2_sized
  pos := srSg2_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The third stage at the radius 10,490. -/
theorem srSg3_J : srSg3.StageJ 10490 where
  sized := srSg3_sized
  pos := srSg3_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The first stage at its radius, spelled as the stage of the link's group. -/
theorem sr_sg_J (eM e0 e1 eU : ℕ) : ((srSz eM e0 e1 eU).sg 97).StageJ 65304 := by
  rw [sr_sg]
  exact srSg1_J

/-- Twice each stage's radius is above the stage's distance. -/
theorem sr_beyond : srSg1.d < 2 * 65304 ∧ srSg2.d < 2 * 10490 ∧ srSg3.d < 2 * 10490 := by
  rw [srSg1_d, srSg2_d, srSg3_d]
  decide

/-- The Johnson bound's lists at the three stages and their radii. -/
theorem sr_lists : srSg1.lstJ 65304 = 241 ∧ srSg2.lstJ 10490 = 516 ∧ srSg3.lstJ 10490 = 516 := by
  unfold Sg.lstJ listMax
  decide +kernel

/-! ## The folds, the code switches, the base case -/

/-- The sizes of the first two stages fit. -/
theorem sr_fit12 : CsFit srSg1 srSg2 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

/-- The sizes of the last two stages fit. -/
theorem sr_fit23 : CsFit srSg2 srSg3 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

/-- The sizes of the first two stages fit, with the first stage as the stage of the link's group. -/
theorem sr_fit12g (eM e0 e1 eU : ℕ) : CsFit ((srSz eM e0 e1 eU).sg 97) srSg2 := by
  rw [sr_sg]
  exact sr_fit12

/-- The rounds of the first stage's fold. -/
theorem sr_fold1 : FoldRounds (srRd 6) (srRd 7) := foldRounds_of sr_rd6 sr_rd7

/-- The rounds of the second stage's fold. -/
theorem sr_fold2 : FoldRounds (srRd 15) (srRd 16) := foldRounds_of sr_rd15 sr_rd16

/-- The two rounds of the first switch: one answer to the sample. -/
theorem sr_rounds12 : CsRounds srSg1 srSg2 (srRd 13) (srRd 14) :=
  csRounds_of sr_rd13 sr_rd14 (by decide)

/-- The same, with the first stage as the stage of the link's group. -/
theorem sr_rounds12g (eM e0 e1 eU : ℕ) :
    CsRounds ((srSz eM e0 e1 eU).sg 97) srSg2 (srRd 13) (srRd 14) := by
  rw [sr_sg]
  exact sr_rounds12

/-- The two rounds of the second switch: one answer to the sample. -/
theorem sr_rounds23 : CsRounds srSg2 srSg3 (srRd 20) (srRd 21) :=
  csRounds_of sr_rd20 sr_rd21 (by decide)

/-- The first round of the base case. -/
theorem sr_lambda : SendsDraws (srRd 22) 1 1 0 0 := rLambda_sd sr_rd22

/-! ## What the first six rounds send and draw -/

/-- The link's five rounds and the batching. -/
theorem sr_batDraws (eM e0 e1 eU : ℕ) :
    BatDraws (srSz eM e0 e1 eU) (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5) :=
  batDraws_of (srSz eM e0 e1 eU) _ _ _ _ _ _ _ _ sr_rd0 sr_rd1 sr_rd2 sr_rd3
    (show srPar.T.a ≤ 64 by decide) sr_rd4 sr_rd5

/-- What the five rounds draw. -/
theorem sr_draws (eM e0 e1 eU : ℕ) :
    DrawsOK (srSz eM e0 e1 eU) (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) :=
  drawsOK_of (sr_batDraws eM e0 e1 eU)

/-- The batching's round sends nothing and draws one element. -/
theorem sr_bat : SendsDraws (srRd 5) 0 1 0 0 := rBatN_sd sr_rd5

/-! ## The tables' code -/

/-- The tables' code and the radius 6,137,119 of the decoder and both folds meet `Sz.RadJ`, and
twice the radius is above the distance 7,798,786. -/
theorem sr_radJ (eU : ℕ) : (srSz 6137119 6137119 6137119 eU).RadJ ∧
    (srSz 6137119 6137119 6137119 eU).dT < 2 * (srSz 6137119 6137119 6137119 eU).eM :=
  Sz.radJ_small rfl rfl rfl rfl rfl rfl

/-- The Johnson bound's list of the tables' code at that radius. -/
theorem sr_list_tables : listMax (2 ^ 23) 7798786 6137119 = 114 := by
  unfold listMax
  decide +kernel

/-! ## The two folded rows -/

/-- The code of the two folded rows: at most 2^32 positions, no more coefficients than positions,
and the radius 65,304 is below its Johnson radius. -/
theorem sr_memb (eM e0 e1 : ℕ) : (srSz eM e0 e1 65304).P.C.a ≤ 32 ∧
    (srSz eM e0 e1 65304).P.C.r + (srSz eM e0 e1 65304).P.C.l ≤
      2 ^ (srSz eM e0 e1 65304).P.C.a ∧
    InJohnson (2 ^ (srSz eM e0 e1 65304).P.C.a)
      (2 ^ (srSz eM e0 e1 65304).P.C.a -
        ((srSz eM e0 e1 65304).P.C.r + (srSz eM e0 e1 65304).P.C.l) + 1)
      (srSz eM e0 e1 65304).eU := by
  show srPar.C.a ≤ 32 ∧ srPar.C.r + srPar.C.l ≤ 2 ^ srPar.C.a ∧
    InJohnson (2 ^ srPar.C.a) (2 ^ srPar.C.a - (srPar.C.r + srPar.C.l) + 1) 65304
  unfold InJohnson
  decide +kernel

/-- A row of the code of the two folded rows has 2^15 places. -/
theorem sr_row_pow (eM e0 e1 eU : ℕ) :
    (srSz eM e0 e1 eU).P.C.l = 2 ^ (srSz eM e0 e1 eU).P.aP := by
  show srPar.C.l = 2 ^ srPar.aP
  decide +kernel

/-- The corners of the layout that is compared are different, at every sample map. -/
theorem sr_pl_inj (eM e0 e1 eU : ℕ) (Z : Sample GE (srSz eM e0 e1 eU).En) :
    Function.Injective ((srSz eM e0 e1 eU).lkR Z).D.pl :=
  lw_pl_inj _ (cut_le_two_pow _)

/-- The corners of a folded row's oracle message are different. -/
theorem sr_memb_plc_inj (eM e0 e1 eU : ℕ) : Function.Injective (srSz eM e0 e1 eU).memb.plc :=
  memb_plc_inj _ (rows_le_two_pow _) (sr_row_pow eM e0 e1 eU).le

end OnBytes.Slice
