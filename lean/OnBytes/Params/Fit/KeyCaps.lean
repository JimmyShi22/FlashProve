-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/KeyCaps.lean: the cap KeyCap of FitPlans.lean (in this folder) holds at the key's
sizes that the planner derives, where the parameter file's lines are within their ranges.

FitPlans.lean shows that every entry of the plans of a key file's chains is Small, under a cap on
the sizes from which the plans are made (KeyCap). This file pays that cap from what sized returns
and the ranges of the lines (LinesCap, LinesCap.lean). It is the twin of reqCap_of_sized
(FitCaps.lean) and gathers what the other files of this folder show: the parts of keySized and the
stages of the proof of the ranges (SizedParts.lean), the test on the table (linCap_of,
FitCaps.lean), the rows (LinRows.lean), the cubes (FitCubes.lean), the codes (CodesSized.lean), the
table (TableCap.lean), the trees (TreesSites.lean), and the test linOk that sized runs itself
(sized_tests, TreesSized.lean).

Main name.
  keyCap_of_sized: KeyCap of the key's sizes that sized returns.

What this file does not claim. LinesCap is a premise. Nothing where sized refuses; that sized
returns at any lines is not said here. The program does not import this file.


-/
import OnBytes.Params.Fit.FitCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

open OnBytes OnBytes.Plan

/-- **KeyCap of the key's sizes that sized returns.** -/
theorem keyCap_of_sized {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z)
    (H : LinesCap l) : KeyCap z.key := by
  obtain ⟨_, _, t3⟩ := sized_tests h
  have ok2 : z.key.once.shape.ok = true := linOk_ok t3
  have hk := sized_key h
  obtain ⟨T, L, rows, codes1, hT, hL, hr, hl, hR⟩ := keySized_parts hk
  have hs := codesShort_of_cap (keySized_codes hk H)
  obtain ⟨cF, cO, cW⟩ := linLines_caps H L.matrixRows rows true
  have hM : L.matrixRows ≤ 2 ^ 64 := by
    have e : z.key.once.shape.matrixRows = L.matrixRows := linSized_matrixRows hl
    have k := (linShape_caps ok2).2.1
    have q : z.key.once.shape.matrixRows ≤ 2 ^ 30 := le_of_ceilLog2 k
    rw [e] at q
    exact q.trans (by omega)
  have tb : TableOk z.key.once.table := by
    rw [linSized_table hl]
    exact tableOk_of_lines H hT
  have N := linNums_of_lines H hT hr hM true
  obtain ⟨_, _, _, _, r5⟩ := lin_rows hl N
  have cR : GroupCap L.group := by
    rw [rangesLines_group hL]
    exact H.onceRanges
  obtain ⟨st, fr⟩ := ranges_stages hR cR
  exact
    { lin := linCap_of z.key.codes hl N cF cO cW tb ok2 hs
      input := cubeBits_le hs r5.1 r5.2
      message := cubeBits_le hs fr.1 fr.2
      trees := fun _ hq => trees_ranges _ _ hq
      test := st }

end OnBytes.Params
