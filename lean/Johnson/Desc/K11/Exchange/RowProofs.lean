-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/RowProofs.lean: the proofs of `RowSaysBehind` and `RowHoldsBehind`
(Johnson/Desc/K11/Exchange/RowStatement.lean), to the letter. Lemmas; none of the library's goals.

How. All by the library's own lemmas. What a row that the reader gives is made of: `row_tie`
(Johnson/Top/H0/MergeLaw/WoRow.lean). The row's weights, summed over the cube against the rows read
at the point, are the merge's function at its point: `pending_port_free`
(Johnson/Road/Rows/StretchLaws.lean); that function is the sum with Gam folded from any number of
zeros: `pending_gamma` (Johnson/Road/FormsKeysMerge.lean). The two notions of "the row holds" are
one: `rowSays_iff_holds`, with `pending_sizes` (Johnson/Top/H0/MergeLaw/RowHolds.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.RowStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open OnBytes (E zeroE oneE mulE TensorRow)
open OnBytes.Model (Reading WsLay WsClaim WsForkOut wsRowPart wsEpsT wsGammaAdd)
open OnBytes.Road (Wm pending_gamma gl_numerals)
open OnBytes.Road.Rows (pending_port_free)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (RowSays row_tie rowSays_iff_holds pending_sizes)
open VerifiableInference.Desc.K13.Law (Wit Holds lowBits)
open Johnson.Desc.First.Walk.Law (rowBy ledgerAt)

/-- **The equation gives "the row holds", said plainly.** -/
theorem rowSaysBehind : RowSaysBehind := by
  intro left lay n lin s wo cr Gam cells idx hleft hrecs hfold hE r hr
  obtain ⟨w0, w, l, c, l', b1, b2, b3, b4, b5, b6, b7, b8⟩ := row_tie hr
  have e0 : w0 = wo := by
    rw [hleft] at b1
    exact (Option.some.inj b1).symm
  subst e0
  obtain ⟨_, _, _, hsum⟩ :=
    pending_port_free Reading.gl gl_numerals lay cells w0 n lin cr hrecs b2
  have hg := pending_gamma gl_numerals lay cells w0.rm cr (n := lay.m0) (Gam := Gam)
    (by rw [← hrecs]; exact hfold)
  have heq := hE l c l' b3 b4
  unfold RowSays
  rw [b5]
  show ∑ j ∈ Finset.range (2 ^ lin.kRow),
      OnBytes.Road.Rows.pendWeight Reading.gl w.g j *
        OnBytes.Road.rowAt Reading.gl lay.lk w.psi.reverse.toArray cells j +
      ([((⟨s.out.indexMasks, c⟩ : OnBytes.Slot), w.beta)].map
        fun x => idx x.1.index * Reading.gl.val x.2).sum = Reading.gl.val w.target
  rw [b6, List.reverse_reverse, Array.toArray_toList, hsum, hg, b7, b8, ← heq]
  simp [mul_comm]

/-- **And so in the pile's own sense.** -/
theorem rowHoldsBehind : RowHoldsBehind := by
  intro left lay n lin s wo cr Gam cells idx nR kC wK hk hleft hrecs hfold hE hn hzero hmat hmask r
    hr
  subst hk
  have hrow := rowSaysBehind left lay n lin s wo cr Gam cells idx hleft hrecs hfold hE r hr
  obtain ⟨w0, w, l, c, l', _, b2, _, _, b5, b6, _, _⟩ := row_tie hr
  refine (rowSays_iff_holds cells idx r wK ?_ hn hzero hmat ?_).1 hrow
  · rw [b5]
    show w.psi.length = lay.lk
    rw [b6, List.length_reverse, Array.length_toList]
    exact (pending_sizes b2).1
  · intro t ht
    rw [b5] at ht
    rw [List.mem_singleton.1 ht]
    exact hmask c

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.rowSaysBehind
#print axioms Johnson.Desc.First.ForkMerge.Exchange.rowHoldsBehind
