-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SameNumbers.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: of a place's
numbers the functions of Johnson/Desc/K8/Honest/Window.lean read three alone: each matrix's columns,
each matrix's rows of cells, and the number of combinations. Statements and proofs. SMALL LEMMAS;
NONE OF THE LIBRARY's GOALS.

  `SameNumbers p q`   two places' numbers are alike in these three
  `entry_same`, `comb_same`, `leaves_same`, `cellsSmall_same`, `allRows_same`, `digitAt_same`
                      then each function is the same function at both
Why: two values of a place's numbers can be made of one list of matrices and differ in what these
functions do not read (the link, the piece, the families of tables, the messages' numbers): a fact
that is shown at the one can then be spent at the other.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest

/-- Two places' numbers are alike in the matrices' columns, their rows of cells and the number of
combinations. -/
structure SameNumbers (p q : Par) : Prop where
  ks : p.ks = q.ks
  ms : p.ms = q.ms
  tau : p.tau = q.tau

variable {p q : Par}

theorem entry_same (h : SameNumbers p q) : entry p = entry q := by
  funext d mu c u
  unfold entry firstColumns
  rw [h.ks, h.tau]

theorem comb_same (h : SameNumbers p q) : comb p = comb q := by
  funext cell d mu i u
  unfold comb
  rw [h.ks, entry_same h]

theorem leaves_same (h : SameNumbers p q) : leaves p = leaves q := by
  funext cell d
  unfold leaves
  rw [h.ks, h.ms, h.tau, comb_same h]

theorem cellsSmall_same (h : SameNumbers p q) : cellsSmall p = cellsSmall q := by
  funext cell
  unfold cellsSmall
  rw [h.ks, h.ms]

theorem allRows_same (h : SameNumbers p q) : allRows p = allRows q := by
  unfold allRows
  rw [h.ms]

theorem digitAt_same (h : SameNumbers p q) : digitAt p = digitAt q := by
  funext cell d u col
  unfold digitAt
  rw [allRows_same h, h.ms, h.tau, comb_same h]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.leaves_same
#print axioms VerifiableInference.Desc.First.K8.Honest.cellsSmall_same
#print axioms VerifiableInference.Desc.First.K8.Honest.digitAt_same
