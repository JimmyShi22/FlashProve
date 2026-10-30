-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefSlots.lean: THE VALUE's FORMULAS FOR THE SLOTS, AT THE REFERENCE SIZES, AS CLOSED
NUMBERS. Evaluations by Lean's kernel of `slotsAt` (Johnson/Road/K4/ValueSlots.lean) at `Dim.ref`,
for a group that is not the first. They are here so that a run of the programs can be held against
them: a check that can fail.

  `ref_kS`: the library's number of variables of the batched sumcheck is 23. `ref_nT`: the library's
    number nNu + ne + ne · nx is 266. `ref_nI`: 2 + (1 + ne) + (6 nl + 4 ne) is 37. That these two
    are the numbers of end values that K4's hearing hears (nEndT y; 2 + (1 + LamM) + NCL) is not
    shown here: Johnson/Road/K4/RefSlotsAt.lean gives the equations, under `Plan4.Meets`.
  `ref_span`: from the first free slot n0 in front of K4's own rounds to the merge's first own slot
    there are 726 slots, whatever n0.
  `ref_behind`: so behind the merge's own slots (1 + 2 lk + 2 more by `hear_end_later`,
    Johnson/Road/K4/HearSlotsEnd.lean; lk is taken as kRef = 18: that the layout's lk is kRef is not
    shown here) the next free slot is n0 + 765.

Limits. Numbers alone. Which number n0 is at a run, and what a run prints, is said in no Lean file.

-/
import Johnson.Road.K4.ValueSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb.Pv.Lay.At (kS)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)

theorem ref_kS : kS Dim.ref = 23 := by decide +kernel

theorem ref_nT : Dim.ref.nNu + Dim.ref.ne + Dim.ref.ne * Dim.ref.nx = 266 := by decide +kernel

theorem ref_nI : 2 + (1 + Dim.ref.ne) + (6 * Dim.ref.nl + 4 * Dim.ref.ne) = 37 := by
  decide +kernel

/-- The formulas at `Dim.ref`, at 266 and 37 end values: from the first free slot in front to the
merge's first own slot. -/
theorem ref_span (n0 : ℕ) : (slotsAt Dim.ref n0 266 37).f7 = n0 + 726 := by
  have e : (slotsAt Dim.ref 0 266 37).f7 = 726 := by decide +kernel
  have s : (slotsAt Dim.ref n0 266 37).f7 = n0 + (slotsAt Dim.ref 0 266 37).f7 := by
    simp only [slotsAt]
    omega
  rw [s, e]

/-- The formulas at `Dim.ref`, at 266 and 37 end values: the merge's first own slot + 1 + 2 kRef +
2. -/
theorem ref_behind (n0 : ℕ) : (slotsAt Dim.ref n0 266 37).f7 + 1 + 2 * kRef + 2 = n0 + 765 := by
  rw [ref_span]
  show n0 + 726 + 1 + 2 * 18 + 2 = n0 + 765
  omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ref_kS
#print axioms OnBytes.Road.K4.ref_nT
#print axioms OnBytes.Road.K4.ref_nI
#print axioms OnBytes.Road.K4.ref_span
#print axioms OnBytes.Road.K4.ref_behind
