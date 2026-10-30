-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/NumsAtFull.lean: the proofs of `ColBitsAtFull`, `RowGivenFits`,
`RowsFitAtFull` and `PlaceOfLot` (Johnson/Desc/K11/Exchange/NumsAtFullStatement.lean), to the
letter. Lemmas; none of the library's goals.

How. All by the library's own lemmas. The ground is the blank ground of the public part
(`IM.base_made`, Johnson/IMR/PureJoin.lean); the test gives the equations (`nums_of_test`,
`hlay_at`, Johnson/Top/H0/MergeLaw/PlanNumsAt.lean); the data's terms are, by definition, those of
which these speak. Where the reader gives a row its text has returned (`rowAt_some`,
Johnson/Top/H0/Walk/FrameRow.lean), and just when it returns is written out (`pendingRowO_iff`,
Johnson/Desc/First/Pend/RowMeans.lean). The place: by definition, the lot's piece being 9.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.NumsAtFullStatement
import Johnson.Desc.First.Pend.RowMeans
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc.First.MergeLaw (nums_of_test hlay_at numsB nsB nRB kColB)
open Johnson.Desc.First.Walk.Law (rowAt_some)

/-- **The column bits, and the index.** -/
theorem colBitsAtFull : ColBitsAtFull := by
  intro Z D r Zp Np cF x h Bs hmade tn
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made hmade).2.2.1
  obtain ⟨_, n3, n4⟩ := nums_of_test hG tn
  refine ⟨?_, n3⟩
  rw [← hlay_at hG]
  exact n4.symm

/-- **One of the reader's own tests.** -/
theorem rowGivenFits : RowGivenFits := by
  intro lay n lin s r h
  obtain ⟨w, os, _, hp⟩ := rowAt_some.1 h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h12, _⟩ :=
    (VerifiableInference.Desc.First.Pend.pendingRowO_iff lay _ w n lin _ os r).1 hp
  exact h12

/-- **The rows fit, wherever the reader gives a row.** -/
theorem rowsFitAtFull : RowsFitAtFull := by
  intro Z D r Zp Np cF x h n s row tn hrow
  unfold numsB nsB nRB kColB at tn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at tn
  have e : OnBytes.Flat.numsFull.rows = h.𝔇.d1.lay.m0 := tn.1.2
  exact Nat.le_trans (Nat.le_of_eq e) (rowGivenFits _ n _ s row hrow)

/-- **The place.** -/
theorem placeOfLot : PlaceOfLot := by
  intro Z G h
  show (⟨1, some (K11.parOf Z G).link, (K11.parOf Z G).piece, .K11⟩ :
    VerifiableInference.Desc.Place) = IM.k11Place
  rw [h]
  rfl

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.colBitsAtFull
#print axioms Johnson.Desc.First.ForkMerge.Exchange.rowGivenFits
#print axioms Johnson.Desc.First.ForkMerge.Exchange.rowsFitAtFull
#print axioms Johnson.Desc.First.ForkMerge.Exchange.placeOfLot
