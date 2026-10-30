-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Know.lean: knowledge soundness of the smallness test's own round, proved for every size
with `Size.OK` and all letters.

The count is the library's: Alg/Range.lean, `Alg.cnt_allPass_le`: if some column of some matrix has
no small cells behind it, all tau combinations of all matrices can pass for at most one part in
2 ^ tau of the matrices that can be drawn. What is added here: digits in their tables that meet the
ties and the reads give integers in the window that do (`allPass_of_relOut`); the rule for a round
in which the verifier draws (`TWhole.knowAt_draw`, Cb/G6/Join.lean) does the rest.

Main names: `allPass_of_relOut`, `cnt_bad_le`, `knowAt`, `know`.

Limits: as in Cb/Pv/Tail/Block.lean. Above all: M must hold only what is committed before the matrix
is drawn: the symbols, those of earlier sub-proofs too, and the reads. The digits, and whatever else
is sent after the draw, belong to W. At letters whose M holds something that is sent after the draw,
the statement stays true and says nothing of the protocol.

Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Tail.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop Prob

variable {K : Type} [CommRing K] {s : Size} (Λ : Letters K s)

/-- Digits in their tables that meet the ties and the reads: every combination can pass. -/
theorem allPass_of_relOut (hs : s.OK) {x : Λ.X} {β : Dr s} {msg : Λ.M} {Z : Dig K s}
    (h : relOut Λ x β msg Z) : (Λ.fixed x msg).AllPass (s.beta : ℤ) (s.rad : ℤ) β := by
  intro μ u
  obtain ⟨hd, hT, hR⟩ := h
  choose dl hl el using fun i => (hd μ u i).1
  choose dh hh eh using fun i => (hd μ u i).2
  have hc : ∀ i,
      (((dl i : ℤ) + (s.lo : ℤ) * (dh i : ℤ) - (s.beta : ℤ) : ℤ) : K) = comb Z μ u i := by
    intro i
    unfold comb
    rw [el i, eh i]
    push_cast
    ring
  refine ⟨fun i => (dl i : ℤ) + (s.lo : ℤ) * (dh i : ℤ) - (s.beta : ℤ), fun i => ⟨?_, ?_⟩,
    fun i' => ?_, fun r => ?_⟩
  · have : (0 : ℤ) ≤ (dl i : ℤ) + (s.lo : ℤ) * (dh i : ℤ) := by positivity
    linarith
  · have h1 : (dl i : ℤ) + 1 ≤ (s.lo : ℤ) := by exact_mod_cast hl i
    have h2 : (dh i : ℤ) + 1 ≤ (s.hi : ℤ) := by exact_mod_cast hh i
    have h3 : (s.lo : ℤ) * ((dh i : ℤ) + 1) ≤ (s.lo : ℤ) * (s.hi : ℤ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (s.lo : ℤ) * (s.hi : ℤ) ≤ 2 * (s.beta : ℤ) := by exact_mod_cast hs
    linarith
  · rw [← Alg.pack_intCast]
    have e : (fun i => (((dl i : ℤ) + (s.lo : ℤ) * (dh i : ℤ) - (s.beta : ℤ) : ℤ) : K)) =
        comb Z μ u := funext hc
    rw [e]
    exact hT μ u i'
  · exact (hR μ u r).trans
      (Finset.sum_congr rfl fun i _ => congrArg (Λ.w x μ r i * ·) (hc i).symm)

/-- The count: for each tuple of messages, at most one part in 2 ^ tau of the matrices lead from
messages without cells to digits that meet all clauses. -/
theorem cnt_bad_le (hs : s.OK) (x : Λ.X) (y : Λ.E.Str) (msg : Λ.M) :
    cnt (fun β : Dr s => ∃ wp, (B Λ).relR ((x, β), y) (msg, wp) ∧ ¬ (A Λ).relR (x, y) (msg, wp)) ≤
      Fintype.card (Dr s) / 2 ^ s.tau := by
  by_cases hg : relIn Λ x msg
  · refine le_trans (le_of_eq (cnt_false ?_)) (Nat.zero_le _)
    rintro β ⟨wp, hB, hA⟩
    exact hA ⟨hB.1, hg⟩
  · have hcnt := Alg.cnt_allPass_le (U := Fin s.tau) (Λ.fixed x msg) hg
    rw [Fintype.card_fin] at hcnt
    refine le_trans (cnt_mono ?_) hcnt
    rintro β ⟨wp, hB, -⟩
    exact allPass_of_relOut Λ hs hB.2

/-- The block's soundness property, whole. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
theorem knowAt (hs : s.OK) : TWhole.KnowAt (R Λ) (A Λ) (B Λ) (fun _ _ _ wp => wp) (eps Λ) :=
  TWhole.knowAt_draw Prod.mk (A Λ) (B Λ) (Fintype.card (Dr s) / 2 ^ s.tau)
    (fun _ _ _ _ => trivial) fun x y msg _ => cnt_bad_le Λ hs x y msg

/-- Knowledge soundness of the round: the statement of Cb/Pv/Tail/Block.lean. This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. -/
theorem know (hs : s.OK) : HoleAt Λ := (knowAt Λ hs).know

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.allPass_of_relOut
#print axioms Cb.Pv.Tail.cnt_bad_le
#print axioms Cb.Pv.Tail.knowAt
#print axioms Cb.Pv.Tail.know
