-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwRows16.lean.
The list of rows of an assembled lookup's read-out is the flat function's list of rows, all but its
last, spread.

States: `rows16_eq`: the list of rows that the read-out A.rd hands on at the last state o,
(A.rd o).2.2, is the flat function TwV.rowsOfTrace at the numbers numsOf A (A.rd o).1 kAt and the
trace of o, all but its last row, spread by toRow: for every A : LkAsmH E, every o : A.XB (reached
by a run or not), every kAt. No premise. `rows2_eq`: the tie's rows in the trace's words.
Limits: kAt is an idle letter here: of the flat function's rows only the last, the keys' row
(TwV.rowKey), reads it.
Does not say: anything on that last row (the list of A.rd holds no such row: A.rd hands on the
masked claim on the keys, (A.rd o).2.1, on which nothing is said here), on a transcript, or on
which states a run reaches.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwRows

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp

variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E) (o : A.XB)

theorem rows2_eq : A.rows2 (A.oR (A.o4 (A.oldT o))) =
    (tieRowsR (numsOf A (A.rd o).1 kAt) (traceOf A o).lam (traceOf A o).tie.reverse).map toRow := by
  rw [show (traceOf A o).tie.reverse = tieN A.H.tie (A.n + 1) (A.oR (A.o4 (A.oldT o))).2 from
      List.reverse_reverse _]
  exact tie_rows A kAt (A.n + 1) (A.oR (A.o4 (A.oldT o))).2

theorem rows16_eq : (A.rd o).2.2 =
    ((rowsOfTrace (numsOf A (A.rd o).1 kAt) (traceOf A o)).dropLast).map toRow := by
  unfold rowsOfTrace
  rw [List.dropLast_concat]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [← rows2_eq A kAt o, ← rows4_eq A kAt (A.rd o).1 o, show (numsOf A (A.rd o).1 kAt).w = A.w from
      rfl,
    ← rowsT_eq A kAt (A.rd o).1 o, ← end_eq A kAt o,
    ← bitU_eq A kAt (A.rd o).1 o, ← bitE_eq A kAt (A.rd o).1 o, ← num_eq A kAt (A.rd o).1]
  rfl

end Tw3
#print axioms Tw3.rows2_eq
#print axioms Tw3.rows16_eq
