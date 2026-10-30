-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/WfGlCount.lean: at the reference numbers of weights-formedness (two lookups of 2^40 keys into
tables of 2^8 and 2^13 entries; multiplicities of 41 digits on 6 position variables; 18 column
variables): how many digits, how many masks of the first and of the second message: three numerals.

One definition, one statement (`Cm.WfGl.Spec.xRef_count`) and its proof: Cb/Ld/LdBldWfCount.lean
evaluated. A forest (`BldWfN.Fo`) is the number f ≤ n of one of the lookups, here 0 or 1; the digits
(`BldWfN.Bit`, Cb/Ld/LdBldWf.lean) are indexed by a forest f, one of 2^(d f) table entries and one
of 2^(w f) positions (n, d, w: fields of `BldWfN`).

Main names:
  `xRef k`: the numbers of the builder (`BldWfN`, Cb/Ld/LdBldWf.lean): forests 0, 1; k column
    variables (a parameter, so that a term that is 18 can stand there); 22 key row variables; the
    tables of `keysGl`; 6 position variables; 41 digits count.
  `Spec.xRef_count`: for k = 18: the digits: 540,672 (= (2^8 + 2^13) · 2^6); own masks of the two
    lookups: 2,257 and 2,462; the first message's masks: 4,715 (all of these but the four inner
    masks of the last levels); the second message's masks: 41 (these four, and the 37 hiding
    coefficients of the batching).

Limits: this file does not say that the width 41 and the 6 position variables are the least that fit
(for the width: Cm/WfGlKeys.lean: 41 ≤ w ≤ 50); by reading, a write-up of ours
(lean/CREDITS.md) prints no width.
This file does not say how many data and free entries the messages have.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cm.WfGlKeys
import Cb.Ld.LdBldWfCount

set_option autoImplicit false

namespace Cm.WfGl
open Cb Finset

/-- The numbers at the reference. -/
@[reducible] def xRef (k : ℕ) : BldWfN :=
  ⟨1, k, fun _ => 22, keysGl.tabVars, fun _ => 6, fun _ => 40⟩

def Spec.xRef_count : Prop :=
  ∀ k, k = 18 →
    Nat.card (xRef k).Bit = 540672 ∧
    (xRef k).own 0 = 2257 ∧
    (xRef k).own 1 = 2462 ∧
    Nat.card ((xRef k).Msk1 Gl.E) = 4715 ∧
    Nat.card ((xRef k).Msk2 Gl.E) = 41

theorem xRef_count : Spec.xRef_count := by
  intro k hk
  subst hk
  have o0 : (xRef 18).own 0 = 2257 := by decide
  have o1 : (xRef 18).own 1 = 2462 := by decide
  refine ⟨?_, o0, o1, ?_, ?_⟩
  · rw [bldWfC_bit, sum_range_succ, sum_range_succ, sum_range_zero]
    decide
  · have h := bldWfC_one (xRef 18) Gl.E
    rw [sum_range_succ, sum_range_succ, sum_range_zero, o0, o1] at h
    have h' : Nat.card ((xRef 18).Msk1 Gl.E) + 2 * (1 + 1) = 0 + 2257 + 2462 := h
    omega
  · exact bldWfC_two (xRef 18) Gl.E

end Cm.WfGl
