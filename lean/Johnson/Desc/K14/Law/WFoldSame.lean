--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/WFoldSame.lean: THE TWO SENTENCES ARE ONE: "W's message holds g^T M" as the
linear claim's first part says it (WIs: the columns by their bits, W read off the words) and as the
shared part says it in front of "LIN point" (VIs: rows and columns by their numbers, a vector).
A theorem: algebra; no challenge, no record.

  numbers_of_wis   WIs at a matrix by numbers gives the sentence with numbers: the converse of the
                   first part's wis_by_numbers.
  wis_iff_vis      Spec.same (Johnson/Desc/K14/Law/WFoldSpec.lean), proved.
What is not claimed. That either sentence holds anywhere. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.WFoldSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open VerifiableInference.Desc.K13.Law (EvalAt WIs matBy wis_by_numbers ofBits_low lowBits ρg)

/-- WIs at a matrix by numbers gives the sentence with numbers. -/
theorem numbers_of_wis {nR k : ℕ} (T : ℕ → ℕ → GE) (g V : ℕ → GE) (m : Words GE)
    (gs : List Tensor) (w : ℕ) (lay : VectorLay)
    (hg : ∀ y < nR, g y = (gs.map fun t => ρg.val (t.entry y)).sum)
    (hvec : ∀ c < 2 ^ k, m w .main (lay.index c) = V c)
    (h : WIs (matBy (nR := nR) k T) m gs w lay) :
    ∀ c < 2 ^ k, V c = ∑ y ∈ Finset.range nR, g y * T y c := by
  intro e he
  rw [← hvec e he, h e he, ← Fin.sum_univ_eq_sum_range (fun y => g y * T y e) nR]
  refine Finset.sum_congr rfl fun i _ => ?_
  show VerifiableInference.Desc.K13.Law.weights ρg nR gs i * T i (Nat.ofBits (lowBits k e)) =
    g i * T i e
  rw [ofBits_low he, hg i i.2]
  rfl

/-- **The two houses' sentences are one.** -/
theorem wis_iff_vis : Spec.same := by
  intro S D m Tab g V hg hvec
  exact ⟨fun h => numbers_of_wis (matOf S.kLo Tab) g V m D.row.g D.w D.lay hg hvec h,
    fun h => wis_by_numbers (matOf S.kLo Tab) g V m D.row.g D.w D.lay hg hvec h⟩

end Desc.K14.Law
