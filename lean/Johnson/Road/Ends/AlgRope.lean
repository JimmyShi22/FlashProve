-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgRope.lean: one Bool on public numbers from which the rotary tables' agreement
follows.
States: (agreeT_of_ropeOK) AgreeT D tb (tbG P) L0 (Johnson/Road/Ends/AlgCongr.lean: the library's
rotary tables are the verifier's, at the segment's layers, its positions and the pairs of channels
of a head) follows from one Bool on public numbers, ropeOK.
Does not say: that ropeOK is true at any tables. A run of it:
Johnson/Road/Ends/GuardRope.lean.
-/
import Johnson.Road.Ends.AlgCongr
import Johnson.Road.Ends.AlgWit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim)

/-- Whether the tables tb have the verifier's rotary entries, inside the ranges that the keys
read. -/
def ropeOK (P : Model.Layer.Pub) (D : Dim) (tb : Tables) (L0 : ℕ) : Bool :=
  (List.range D.nl).all fun l => (List.range D.T).all fun i =>
    (List.range (D.P.ch / 2)).all fun jj =>
      decide (tb.C (L0 + l) i jj = (tbG P).C (L0 + l) i jj) &&
        decide (tb.S (L0 + l) i jj = (tbG P).S (L0 + l) i jj)

/-- **If so, the two tables agree in the sense of AgreeT.** -/
theorem agreeT_of_ropeOK {P : Model.Layer.Pub} {D : Dim} {tb : Tables} {L0 : ℕ}
    (h : ropeOK P D tb L0 = true) : AgreeT D tb (tbG P) L0 := by
  have key : ∀ l < D.nl, ∀ i < D.T, ∀ jj < D.P.ch / 2,
      tb.C (L0 + l) i jj = (tbG P).C (L0 + l) i jj ∧
        tb.S (L0 + l) i jj = (tbG P).S (L0 + l) i jj := by
    intro l hl i hi jj hj
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h l
      (List.mem_range.mpr hl)) i (List.mem_range.mpr hi)) jj (List.mem_range.mpr hj)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h1
  exact ⟨fun l hl i hi jj hj => (key l hl i hi jj hj).1,
    fun l hl i hi jj hj => (key l hl i hi jj hj).2⟩

#print axioms agreeT_of_ropeOK

end OnBytes.Road.Alg
