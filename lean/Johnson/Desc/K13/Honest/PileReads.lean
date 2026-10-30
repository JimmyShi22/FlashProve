--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/PileReads.lean: kind K13, the members' batching: OF THE PILE THE HONEST
PROVER's ROUNDS READ THE ROWS' NUMBER, WEIGHTS AND COLUMN POINTS ALONE: two piles that agree in
these give the same tables (`tabsOf`) and the same rounds (`movesAtM3`,
Johnson/Desc/K13/Honest/MovesAtM3.lean). Two definitions, and statements with their proofs.

Why. In the verifier's state a row's target is a value that the prover has sent. A prover that makes
the pile's rows anew, of public data and challenges, cannot make the target. It could make the mask
form (slots and coefficients are made of public data and challenges); it need make neither.
Main names:
  `rowReads r`: a row's weights and column point.
  `tabsOfL`, `tabsOf_eq`: the tables as a function of the rows' weights and column points.
  `tabsOf_congr`, `movesAtM3_congr`: **the two statements.**

What is not claimed. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.MovesAtM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K13.Law

variable {K : Type} [Field K] (ρ : Reading K) {nR k : ℕ}

/-- A row's weights and column point. -/
def rowReads (r : TensorRow) : List Tensor × List E := (r.g, r.psi)

/-- The tables, of the rows' weights and column points. -/
def tabsOfL (w : Wit K nR k) (L : List (List Tensor × List E)) (a : K) : List (List K × List K) :=
  List.ofFn fun q : Fin L.length =>
    (scaleT (a ^ (q : ℕ)) (eqT ((L.get q).2.map ρ.val)),
      tabOf k (colOf w (weights ρ nR (L.get q).1)))

/-- The tables are that function of the pile. -/
theorem tabsOf_eq (w : Wit K nR k) (pile : List TensorRow) (a : K) :
    tabsOf ρ w pile a = tabsOfL ρ w (pile.map rowReads) a := by
  apply List.ext_getElem
  · simp [tabsOf, tabsOfL]
  · intro i h1 h2
    simp [tabsOf, tabsOfL, rowReads]

/-- **Two piles that agree in the rows' weights and column points give the same tables.** -/
theorem tabsOf_congr (w : Wit K nR k) {pile pile' : List TensorRow}
    (h : pile.map rowReads = pile'.map rowReads) (a : K) : tabsOf ρ w pile a = tabsOf ρ w pile' a :=
      by
  rw [tabsOf_eq, tabsOf_eq, h]

/-- **They give the same rounds.** -/
theorem movesAtM3_congr (σ : K → E) (w : Wit K nR k) {pile pile' : List TensorRow}
    (h : pile.map rowReads = pile'.map rowReads) (fresh : List Slot) (x eps : E) (gs : List E) :
    movesAtM3 ρ σ w pile fresh x eps gs = movesAtM3 ρ σ w pile' fresh x eps gs := by
  unfold movesAtM3
  rw [tabsOf_congr ρ w h]

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.tabsOf_eq
#print axioms VerifiableInference.Desc.K13.Honest.tabsOf_congr
#print axioms VerifiableInference.Desc.K13.Honest.movesAtM3_congr
