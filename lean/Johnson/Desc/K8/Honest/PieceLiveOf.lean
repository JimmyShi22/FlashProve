-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/PieceLiveOf.lean: the proofs of the four statements of
Johnson/Desc/K8/Honest/PieceLiveOfStatement.lean, to the letter, and one helper. Lemmas; none of the
library's goals.

How. The plain product is the product of its factors in their order (`eqPlainF_pre`,
Johnson/Desc/K8/Honest/EqRunPlain.lean); a factor is a coordinate or 1 minus it (`eqFactor`, there):
where every coordinate reads as neither 0 nor 1, neither reads as 0; so no product of the first n
does, for n up to the point's size (`eqPre_ne`: by induction on n). The run's value is the plain
product (`eqAt_plain`, there). The call's weight is the coordinate or 1 minus it, by its text. The
title's statement: its three clauses are these three.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K8.Honest.PieceLiveOfStatement
import Johnson.Desc.K8.Honest.EqRunPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims (eqAt)

/-- Where every coordinate reads as neither 0 nor 1: the product of the first n factors does not
read as 0, for n up to the point's size. -/
theorem eqPre_ne (z : Array E) (idx : Nat)
    (h : ∀ v, v < z.size →
      Reading.gl.val (z.getD v zeroE) ≠ 0 ∧ Reading.gl.val (z.getD v zeroE) ≠ 1) :
    ∀ n, n ≤ z.size → Reading.gl.val (eqPre z idx n) ≠ 0
  | 0, _ => by
    show Reading.gl.val oneE ≠ 0
    rw [Reading.gl.one]
    exact one_ne_zero
  | n + 1, hn => by
    show Reading.gl.val (mulE (eqPre z idx n) (eqFactor z idx n)) ≠ 0
    rw [Reading.gl.mul]
    refine mul_ne_zero (eqPre_ne z idx h n (Nat.le_of_succ_le hn)) ?_
    obtain ⟨h0, h1⟩ := h n hn
    unfold eqFactor
    split
    · exact h0
    · rw [Reading.gl.sub, Reading.gl.one]
      exact sub_ne_zero.2 (Ne.symm h1)

/-- **The plain product does not read as 0.** -/
theorem eqPlainFNe : EqPlainFNe := by
  intro z idx h
  rw [eqPlainF_pre]
  exact eqPre_ne z idx h z.size (Nat.le_refl _)

/-- **Nor does the run's value.** -/
theorem eqAtNe : EqAtNe := by
  intro z first i h
  rw [eqAt_plain]
  exact eqPlainFNe z (first + i) h

/-- **Nor does the call's weight by the second computation.** -/
theorem callWeightAgainNe : CallWeightAgainNe := by
  intro g q h
  obtain ⟨h0, h1⟩ := h
  unfold callWeightAgain
  split
  · rw [Reading.gl.sub, Reading.gl.one]
    exact sub_ne_zero.2 (Ne.symm h1)
  · exact h0

/-- **`PieceLive` from "neither 0 nor 1".** -/
theorem pieceLive_of_fine : PieceLiveOfFine := by
  intro tl g W h0 hk w hw
  exact ⟨callWeightAgainNe g w.call h0, fun cc _ => eqAtNe _ _ cc (hk w hw),
    fun r _ => eqPlainFNe _ _ (hk w hw)⟩

end VerifiableInference.Desc.First.K8.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPre_ne
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPlainFNe
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAtNe
#print axioms VerifiableInference.Desc.First.K8.Honest.callWeightAgainNe
#print axioms VerifiableInference.Desc.First.K8.Honest.pieceLive_of_fine
