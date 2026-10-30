-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecCodes.lean: the facts on sizes, radii, rounds and corners that the theorem
`link_chain_joh` (OnBytes/Slice/LinkChainJoh.lean) asks, at the full-size files of the setting
"record with work".

The like of OnBytes/Slice/SmallRecCodes.lean, whose head describes what is asked, at the full size;
its text was made from that file's by a program that swaps names and numbers and writes five stages
for three. The sizes are `frSz`, the stages `frSg1` to `frSg5`, the rounds `frRd`
(OnBytes/Slice/FullRecSz.lean). The radii: 2,852,142,980 for the stored tables' decoder and both
folds; 8,342,420 for the first stage and for a folded row's oracle message; 1,569,886, 98,104, 6,044
and 13,370 for the later stages. All are beyond half the distance of their code and below its
Johnson radius.

Main theorems.
 `frSg1_group` and its like, `fr_positions`   the five stages have the sizes of the planner's five
               groups, and the planner's numbers of positions.
 `frSg1_sized`, `frSg1_pos`, `frSg1_d` and their like   the stages meet `Sg.Sized` and `Sg.Pos`;
               their distances are 12,582,816, 1,966,032, 122,832, 7,631 and 15,833,
               each that of the main rows.
 `frSg1_J` to `frSg5_J`, `fr_sg_J`   the stages meet `Sg.StageJ` at their radii.
 `fr_beyond`   twice each radius is above the distance. `fr_lists`: the Johnson bound's lists there
               are 91, 274, 472, 714 and 712; `fr_list_tables`: that of the tables' code is 26.
 `fr_fit12` and its like, `fr_fit12g`, `fr_rounds12` and its like, `fr_rounds12g`, `fr_fold1` and
 its like, `fr_lambda`   sizes and rounds at the folds, the code switches and the base case.
 `fr_batDraws`, `fr_draws`, `fr_bat`   what the first six rounds send and draw.
 `fr_radJ`     the tables' code and its three radii meet `Sz.RadJ`, beyond half the distance.
 `fr_memb`     the code of the two folded rows, and its radius below the Johnson radius.
 `fr_row_pow`, `fr_pl_inj`, `fr_memb_plc_inj`   a row has 2^22 places; corners are different.

Not claimed. That the radii are the typed parameters' (the planner's distances times the lengths,
rounded down; the planner itself has no radii in whole positions): OnBytes/Slice/FullRecRadii.lean
[not in this library] holds them against the values typed under OnBytes/Params/. Nothing on the
sizes of error counts but the six lists: `bchksBound` is evaluated nowhere here. Nothing on a
protocol, a decision or a file.

-/
import OnBytes.Slice.BatAt
import OnBytes.Slice.CornersAt
import OnBytes.Slice.CsMet
import OnBytes.Slice.DrawsOKOf
import OnBytes.Slice.GroupFit
import OnBytes.Slice.LinkRecBchks
import OnBytes.Slice.ManyHoldsJoh
import OnBytes.Slice.FullRecRounds

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Cb.Ood _root_.Run _root_.Run.PQ

/-! ## The five stages -/

/-- The first stage has the sizes of the planner's first group. -/
theorem frSg1_group : frSg1.FitsGroup Params.recordG1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The second stage has the sizes of the planner's second group. -/
theorem frSg2_group : frSg2.FitsGroup Params.recordG2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The third stage has the sizes of the planner's third group. -/
theorem frSg3_group : frSg3.FitsGroup Params.recordG3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fourth stage has the sizes of the planner's fourth group. -/
theorem frSg4_group : frSg4.FitsGroup Params.recordG4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fifth stage has the sizes of the planner's fifth group. -/
theorem frSg5_group : frSg5.FitsGroup Params.recordG5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The stages' numbers of positions are the planner's. -/
theorem fr_positions :
    Params.recordStages.map (·.t) = [frSg1.t, frSg2.t, frSg3.t, frSg4.t, frSg5.t] := rfl

/-- The first stage meets what is asked of a stage's sizes. -/
theorem frSg1_sized : frSg1.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The second stage meets what is asked of a stage's sizes. -/
theorem frSg2_sized : frSg2.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The third stage meets what is asked of a stage's sizes. -/
theorem frSg3_sized : frSg3.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The fourth stage meets what is asked of a stage's sizes. -/
theorem frSg4_sized : frSg4.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The fifth stage meets what is asked of a stage's sizes. -/
theorem frSg5_sized : frSg5.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- Each code of the first stage has a coefficient. -/
theorem frSg1_pos : frSg1.Pos := ⟨by decide, by decide⟩

/-- Each code of the second stage has a coefficient. -/
theorem frSg2_pos : frSg2.Pos := ⟨by decide, by decide⟩

/-- Each code of the third stage has a coefficient. -/
theorem frSg3_pos : frSg3.Pos := ⟨by decide, by decide⟩

/-- Each code of the fourth stage has a coefficient. -/
theorem frSg4_pos : frSg4.Pos := ⟨by decide, by decide⟩

/-- Each code of the fifth stage has a coefficient. -/
theorem frSg5_pos : frSg5.Pos := ⟨by decide, by decide⟩

/-- The distance of the first stage: 2^24 - 4,194,401 + 1, that of its main rows. -/
theorem frSg1_d : frSg1.d = 12582816 := by decide

/-- The distance of the second stage: 2^21 - 131,121 + 1, that of its main rows. -/
theorem frSg2_d : frSg2.d = 1966032 := by decide

/-- The distance of the third stage: 2^17 - 8,241 + 1, that of its main rows. -/
theorem frSg3_d : frSg3.d = 122832 := by decide

/-- The distance of the fourth stage: 2^13 - 562 + 1, that of its main rows. -/
theorem frSg4_d : frSg4.d = 7631 := by decide

/-- The distance of the fifth stage: 2^14 - 552 + 1, that of its main rows. -/
theorem frSg5_d : frSg5.d = 15833 := by decide

/-- The first stage at the radius 8,342,420: sizes in order, two coefficients or more in each code,
and the radius below the stage's Johnson radius. -/
theorem frSg1_J : frSg1.StageJ 8342420 where
  sized := frSg1_sized
  pos := frSg1_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The second stage at the radius 1,569,886: sizes in order, two coefficients or more in each code,
and the radius below the stage's Johnson radius. -/
theorem frSg2_J : frSg2.StageJ 1569886 where
  sized := frSg2_sized
  pos := frSg2_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The third stage at the radius 98,104: sizes in order, two coefficients or more in each code,
and the radius below the stage's Johnson radius. -/
theorem frSg3_J : frSg3.StageJ 98104 where
  sized := frSg3_sized
  pos := frSg3_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The fourth stage at the radius 6,044: sizes in order, two coefficients or more in each code,
and the radius below the stage's Johnson radius. -/
theorem frSg4_J : frSg4.StageJ 6044 where
  sized := frSg4_sized
  pos := frSg4_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The fifth stage at the radius 13,370: sizes in order, two coefficients or more in each code,
and the radius below the stage's Johnson radius. -/
theorem frSg5_J : frSg5.StageJ 13370 where
  sized := frSg5_sized
  pos := frSg5_pos
  twoC := by decide
  twoZ := by decide
  rad := by decide
  joh := by
    unfold Sg.InJ InJohnson
    decide +kernel

/-- The first stage at its radius, spelled as the stage of the link's group. -/
theorem fr_sg_J (eM e0 e1 eU : ℕ) : ((frSz eM e0 e1 eU).sg 97).StageJ 8342420 := by
  rw [fr_sg]
  exact frSg1_J

/-- Twice each stage's radius is above the stage's distance. -/
theorem fr_beyond :
    frSg1.d < 2 * 8342420 ∧ frSg2.d < 2 * 1569886 ∧ frSg3.d < 2 * 98104 ∧ frSg4.d < 2 * 6044 ∧
    frSg5.d < 2 * 13370 := by
  rw [frSg1_d, frSg2_d, frSg3_d, frSg4_d, frSg5_d]
  decide

/-- The Johnson bound's lists at the five stages and their radii. -/
theorem fr_lists :
    frSg1.lstJ 8342420 = 91 ∧ frSg2.lstJ 1569886 = 274 ∧ frSg3.lstJ 98104 = 472 ∧ frSg4.lstJ 6044 =
    714 ∧ frSg5.lstJ 13370 = 712 := by
  unfold Sg.lstJ listMax
  decide +kernel

/-! ## The folds, the code switches, the base case -/

/-- The sizes of the first and the second stage fit. -/
theorem fr_fit12 : CsFit frSg1 frSg2 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

/-- The sizes of the second and the third stage fit. -/
theorem fr_fit23 : CsFit frSg2 frSg3 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

/-- The sizes of the third and the fourth stage fit. -/
theorem fr_fit34 : CsFit frSg3 frSg4 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

/-- The sizes of the fourth and the fifth stage fit. -/
theorem fr_fit45 : CsFit frSg4 frSg5 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

/-- The sizes of the first two stages fit, with the first stage as the stage of the link's group. -/
theorem fr_fit12g (eM e0 e1 eU : ℕ) : CsFit ((frSz eM e0 e1 eU).sg 97) frSg2 := by
  rw [fr_sg]
  exact fr_fit12

/-- The rounds of the first stage's fold. -/
theorem fr_fold1 : FoldRounds (frRd 6) (frRd 7) := foldRounds_of fr_rd6 fr_rd7

/-- The rounds of the second stage's fold. -/
theorem fr_fold2 : FoldRounds (frRd 17) (frRd 18) := foldRounds_of fr_rd17 fr_rd18

/-- The rounds of the third stage's fold. -/
theorem fr_fold3 : FoldRounds (frRd 25) (frRd 26) := foldRounds_of fr_rd25 fr_rd26

/-- The rounds of the fourth stage's fold. -/
theorem fr_fold4 : FoldRounds (frRd 32) (frRd 33) := foldRounds_of fr_rd32 fr_rd33

/-- The two rounds of the first switch: one answer to the sample. -/
theorem fr_rounds12 : CsRounds frSg1 frSg2 (frRd 15) (frRd 16) :=
  csRounds_of fr_rd15 fr_rd16 (by decide)

/-- The two rounds of the second switch: one answer to the sample. -/
theorem fr_rounds23 : CsRounds frSg2 frSg3 (frRd 23) (frRd 24) :=
  csRounds_of fr_rd23 fr_rd24 (by decide)

/-- The two rounds of the third switch: one answer to the sample. -/
theorem fr_rounds34 : CsRounds frSg3 frSg4 (frRd 30) (frRd 31) :=
  csRounds_of fr_rd30 fr_rd31 (by decide)

/-- The two rounds of the fourth switch: one answer to the sample. -/
theorem fr_rounds45 : CsRounds frSg4 frSg5 (frRd 37) (frRd 38) :=
  csRounds_of fr_rd37 fr_rd38 (by decide)

/-- The first switch's rounds, with the first stage as the stage of the link's group. -/
theorem fr_rounds12g (eM e0 e1 eU : ℕ) :
    CsRounds ((frSz eM e0 e1 eU).sg 97) frSg2 (frRd 15) (frRd 16) := by
  rw [fr_sg]
  exact fr_rounds12

/-- The first round of the base case. -/
theorem fr_lambda : SendsDraws (frRd 39) 1 1 0 0 := rLambda_sd fr_rd39

/-! ## What the first six rounds send and draw -/

/-- The link's five rounds and the batching. -/
theorem fr_batDraws (eM e0 e1 eU : ℕ) :
    BatDraws (frSz eM e0 e1 eU) (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5) :=
  batDraws_of (frSz eM e0 e1 eU) _ _ _ _ _ _ _ _ fr_rd0 fr_rd1 fr_rd2 fr_rd3
    (show frPar.T.a ≤ 64 by decide) fr_rd4 fr_rd5

/-- What the five rounds draw. -/
theorem fr_draws (eM e0 e1 eU : ℕ) :
    DrawsOK (frSz eM e0 e1 eU) (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) :=
  drawsOK_of (fr_batDraws eM e0 e1 eU)

/-- The batching's round sends nothing and draws one element. -/
theorem fr_bat : SendsDraws (frRd 5) 0 1 0 0 := rBatN_sd fr_rd5

/-! ## The tables' code -/

/-- The tables' code and the radius 2,852,142,980 of the decoder and both folds meet `Sz.RadJ`,
and twice the radius is above the distance 3,848,273,922. -/
theorem fr_radJ (eU : ℕ) : (frSz 2852142980 2852142980 2852142980 eU).RadJ ∧
    (frSz 2852142980 2852142980 2852142980 eU).dT <
      2 * (frSz 2852142980 2852142980 2852142980 eU).eM :=
  Sz.radJ_full rfl rfl rfl rfl rfl rfl

/-- The Johnson bound's list of the tables' code at that radius. -/
theorem fr_list_tables : listMax (2 ^ 32) 3848273922 2852142980 = 26 := by
  unfold listMax
  decide +kernel

/-! ## The two folded rows -/

/-- The code of the two folded rows: at most 2^32 positions, no more coefficients than positions,
and the radius 8,342,420 is below its Johnson radius. -/
theorem fr_memb (eM e0 e1 : ℕ) : (frSz eM e0 e1 8342420).P.C.a ≤ 32 ∧
    (frSz eM e0 e1 8342420).P.C.r + (frSz eM e0 e1 8342420).P.C.l ≤
      2 ^ (frSz eM e0 e1 8342420).P.C.a ∧
    InJohnson (2 ^ (frSz eM e0 e1 8342420).P.C.a)
      (2 ^ (frSz eM e0 e1 8342420).P.C.a -
        ((frSz eM e0 e1 8342420).P.C.r + (frSz eM e0 e1 8342420).P.C.l) + 1)
      (frSz eM e0 e1 8342420).eU := by
  show frPar.C.a ≤ 32 ∧ frPar.C.r + frPar.C.l ≤ 2 ^ frPar.C.a ∧
    InJohnson (2 ^ frPar.C.a) (2 ^ frPar.C.a - (frPar.C.r + frPar.C.l) + 1) 8342420
  unfold InJohnson
  decide +kernel

/-- A row of the code of the two folded rows has 2^22 places. -/
theorem fr_row_pow (eM e0 e1 eU : ℕ) :
    (frSz eM e0 e1 eU).P.C.l = 2 ^ (frSz eM e0 e1 eU).P.aP := by
  show frPar.C.l = 2 ^ frPar.aP
  decide +kernel

/-- The corners of the layout that is compared are different, at every sample map. -/
theorem fr_pl_inj (eM e0 e1 eU : ℕ) (Z : Sample GE (frSz eM e0 e1 eU).En) :
    Function.Injective ((frSz eM e0 e1 eU).lkR Z).D.pl :=
  lw_pl_inj _ (cut_le_two_pow _)

/-- The corners of a folded row's oracle message are different. -/
theorem fr_memb_plc_inj (eM e0 e1 eU : ℕ) : Function.Injective (frSz eM e0 e1 eU).memb.plc :=
  memb_plc_inj _ (rows_le_two_pow _) (fr_row_pow eM e0 e1 eU).le

end OnBytes.Slice
