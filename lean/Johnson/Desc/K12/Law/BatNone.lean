-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.TieOkMade
/-
Johnson/Desc/K12/Law/BatNone.lean: the written round "BAT" of a proximity test (the kind K12) sends no tree. One statement and its proof. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  written_bat: wherever the written rounds are there (writtenOf p.nums = some (w0 :: w)), w0.tree = none. No premise beside that equation: by rounds_top (MadeRounds.lean) and layW_quiet (TieOkMade.lean).
WHAT IT PAYS: in the law in the coin (Sheet.lean): the field AtPlace.batNone (dB.trees = []) follows from the field like: Like dB w0 holds dB.trees = w0.tree.toList. The like of AtPlaceOwn.batNone.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf layW)

/-- The written round "BAT" sends no tree. -/
theorem written_bat (N : H2U.TestNums) (w0 : WR) (w : List WR)
    (hw : writtenOf N = some (w0 :: w)) : w0.tree = none := by
  unfold writtenOf at hw
  cases hr : H2U.roundsOfNums N with
  | none =>
    rw [hr] at hw
    cases hw
  | some rds =>
    obtain ⟨_, _, _, R, _, _, rfl⟩ := rounds_top N rds hr
    rw [hr, Option.bind_some, told_shapes, layW_quiet _ _ _ .elems kBat rfl] at hw
    obtain ⟨w1, _, e⟩ := Option.map_eq_some_iff.1 hw
    rw [← (List.cons.inj e).1]
    rfl

end H2K.Made

#print axioms H2K.Made.written_bat
