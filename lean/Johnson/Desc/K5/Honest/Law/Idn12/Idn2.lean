-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean: A SECOND FORM of 2 declarations of
Johnson/Desc/K5/Honest/Law/Idn.lean: `bitSum_zero`, `score_start`.
The source forms take as a premise that the cells meet all three of the library's families of
identities on an attention segment (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean). These take the
first two families alone (`Idn12`, Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean).

Why. CONDITIONALLY, `Idn12` follows from two items that the row of the segment's own rounds asks in
front (Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean): among others under the library's head on the
public input as a hypothesis, hH and hc; none of these, nor the items, is shown. The third family on
the whole cube follows from no such item.

How. THE TEXT IS THE ELDER FILE's: each declaration named above with its docstring and its proof,
the premise's name exchanged, and each name of a declaration that has a second form exchanged for
that form's (a subscript 2 at its end). Every other lemma is called from the elder files, which are
imported and stay as they are.

Limits. Those of the source file, whose head says what each premise is.
Every theorem is conditional.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Idn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K]

/-- **The first two families of identities are 0 at every valid index**: the first two fields of
`AtIdn` (Johnson/Desc/K5/Honest/Law/Idn.lean), to the letter. -/
structure Idn12 (D : Dim) (t : Raw → K) : Prop where
  at1 : ∀ k b g i, Idn.Valid D (.at1 k b g i) → idnVal D t (.at1 k b g i) = 0
  at2 : ∀ b g i, Idn.Valid D (.at2 b g i) → idnVal D t (.at2 b g i) = 0

/-- The three families give the two. -/
theorem AtIdn.idn12 {D : Dim} {t : Raw → K} (h : AtIdn D t) : Idn12 D t := ⟨h.at1, h.at2⟩

/-- **The sum of the sumcheck for the bits is 0**, for any number kap of variables for the number of
a bit. -/
theorem bitSum_zero₂ (kap : ℕ) {D : Dim} {t : Raw → K} (h : Idn12 D t) (p : Pub K) :
    Cb.Pv.Att.bitSum kap D p t = 0 := by
  rw [Cb.Pv.Att.bitSum_mean]
  refine sum_eq_zero fun b hb => ?_
  rw [Blocks.ext_zero_of_forall, mul_zero]
  intro X hX
  unfold Cb.Pv.Att.bitIdnK
  split
  · rename_i hk
    refine h.at1 _ _ _ _ ⟨hk, mem_range.mp hb, Nat.mod_lt _ (Nat.two_pow_pos D.lg), ?_⟩
    rw [Dim.T_eq]
    show X / 2 ^ kap / 2 ^ D.lg < 2 ^ D.lT
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
    calc X < 2 ^ (D.lT + D.lg + kap) := hX
      _ = 2 ^ D.lT * (2 ^ kap * 2 ^ D.lg) := by rw [pow_add, pow_add]; ring
  · rfl

/-- **The sum of step s16 is the batch of the row maxima at (tg, ti).** -/
theorem score_start₂ {D : Dim} {t : Raw → K} (h : Idn12 D t) (C : Calls) (p : Pub K) :
    sumPhi D C p t .s16 = ∑ b ∈ range D.nb, p.o b * rvM6 D p t b := by
  have e := Cb.Pv.Att.scoreMeanG D t C p
  have hz : ∑ b ∈ range D.nb, p.o b * Blocks.ext (D.lg + D.lT) (Cb.Pv.Att.scoreIdnG D t b)
      (cat D.lg p.tg p.ti) = 0 := sum_eq_zero fun b hb => by
    rw [Blocks.ext_zero_of_forall, mul_zero]
    intro Y hY
    refine h.at2 _ _ _ ⟨mem_range.mp hb, ?_, Nat.mod_lt _ (by rw [Dim.T_eq]; positivity)⟩
    show Y / D.T < 2 ^ D.lg
    rw [Dim.T_eq, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact hY
  rw [hz] at e
  exact (sub_eq_zero.mp e).symm

end H2K5.Honest

#print axioms H2K5.Honest.AtIdn.idn12
#print axioms H2K5.Honest.bitSum_zero₂
#print axioms H2K5.Honest.score_start₂
