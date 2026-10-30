-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Idn.lean: what the identities of the library's relation on the cells of
an attention segment give for the sums of its sumchecks, READ FORWARD: from the identities to the
sums. All of it is algebra on the library's definitions (Inst/Model/Att, Cb/Pv/Att/Mean); no text of
the prover or of the verifier is named. Definitions, and statements with their proofs.

The library's relation (`RFraw`, Inst/Model/Att/Trace.lean) asks that three families of identities
are 0 at every valid index: at1 (a cell of the index is a bit), at2 (the row maximum is the score at
the index), at3 (the denominator is the sum of the softmax weights). Cb/Pv/Att/Mean writes the sums
of the sumchecks as extensions of vectors of these identities, as equations at all cells and all
challenges. Its own use of these equations runs from a sum to the identities; here they are spent
the other way.

Main names:
  `AtIdn D t`       the premise: at1, at2 and at3 are 0 at every valid index, at the cells t
  `Rider D C z t`   a weaker premise: the batch of the identities at3 at the lookup's point z is 0
                    (`denOut`, Cb/Pv/Att/Mean/DenStep.lean)
  `idnVal_map`, `AtIdn.map`   the identities commute with a map of fields: cells for which they hold
                    in a field have them in every field above it; meant for the map from the base
                    field, over which the relation is stated, into the extension field of the
                    challenges
  `atIdn_of_int`    cells that are integers with the identities over the integers have them in
                    every field
  `rider_of_at3`, `AtIdn.rider`   at3 at every valid index gives `Rider` at every point
  `bitSum_zero`     under `AtIdn` the sum of the sumcheck for the bits is 0
  `score_start`     under `AtIdn` the sum of step s16 is the batch of the row maxima at (tg, ti)
  `valueProduct_zero`   under `Rider` the sums of steps s11 and s12, less the accumulator's rule
                    value, less th times the denominator's, are 0

Every statement but `idnVal_map` is conditional: on `AtIdn`, on `Rider`, on at3, or, in
`atIdn_of_int`, on the identities over the integers. Who is meant to show `AtIdn`: whoever holds
that the cells are a trace of the relation. No lemma here or in what this file imports gives `Rider`
but `rider_of_at3`.
Limits. Nothing here says that any cells have the identities.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.Mean.Turned
import Cb.Pv.Att.Mean.ValueBelow
import Cb.Pv.Att.Mean.DenStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K]

/-! ## The premises -/

/-- **The three families of identities are 0 at every valid index.** -/
structure AtIdn (D : Dim) (t : Raw → K) : Prop where
  at1 : ∀ k b g i, Idn.Valid D (.at1 k b g i) → idnVal D t (.at1 k b g i) = 0
  at2 : ∀ b g i, Idn.Valid D (.at2 b g i) → idnVal D t (.at2 b g i) = 0
  at3 : ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D t (.at3 b g i) = 0

/-- **The batch of the identities at3 at the lookup's point z is 0.** -/
def Rider (D : Dim) (C : Calls) (z : ℕ → K) (t : Raw → K) : Prop := Cb.Pv.Att.denOut D C z t = 0

/-! ## A map of fields -/

/-- **The identities commute with a map of fields.** -/
theorem idnVal_map {F : Type} [Field F] (φ : F →+* K) (D : Dim) (t : Raw → F) (j : Idn) :
    idnVal D (fun q => φ (t q)) j = φ (idnVal D t j) := by
  have hb : ∀ k j : ℕ, φ (bitR F k j) = bitR K k j := fun k j => by
    unfold bitR
    split_ifs <;> simp
  cases j
  · unfold idnVal ibV
    simp only [map_mul, map_sub, map_one]
  · unfold idnVal mxV qryV sel keyV eq1 ibV
    simp only [map_sub, map_sum, map_mul, map_prod, map_add, map_pow, map_one, map_ofNat, hb]
  · unfold idnVal denV EF rowSum wtV w0 w1
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_one, map_ofNat, apply_ite φ,
      map_zero]

/-- Cells that have the identities in a field have them in every field above it. -/
theorem AtIdn.map {F : Type} [Field F] (φ : F →+* K) {D : Dim} {t : Raw → F} (h : AtIdn D t) :
    AtIdn D fun q => φ (t q) :=
  ⟨fun k b g i hv => by rw [idnVal_map, h.at1 k b g i hv, map_zero],
    fun b g i hv => by rw [idnVal_map, h.at2 b g i hv, map_zero],
    fun b g i hv => by rw [idnVal_map, h.at3 b g i hv, map_zero]⟩

/-- Cells that are integers with the identities over the integers have them in every field. -/
theorem atIdn_of_int {D : Dim} {tz : Raw → ℤ}
    (h : ∀ j : Idn, j.Valid D → idnVal D tz j = 0) : AtIdn D (castT tz : Raw → K) :=
  ⟨fun k b g i hv => by rw [idn_cast, h _ hv, Int.cast_zero],
    fun b g i hv => by rw [idn_cast, h _ hv, Int.cast_zero],
    fun b g i hv => by rw [idn_cast, h _ hv, Int.cast_zero]⟩

/-! ## From the identities to the sums -/

/-- **at3 at every valid index gives the batch 0 at every point.** -/
theorem rider_of_at3 {D : Dim} {t : Raw → K}
    (h : ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D t (.at3 b g i) = 0) (C : Calls)
    (z : ℕ → K) : Rider D C z t := by
  unfold Rider Cb.Pv.Att.denOut rd2
  refine sum_eq_zero fun b hb => ?_
  rw [sum_eq_zero fun g hg => sum_eq_zero fun i hi => by
    show _ * idnVal D t (.at3 b g i) = 0
    rw [h b g i ⟨mem_range.mp hb, mem_range.mp hg, mem_range.mp hi⟩, mul_zero], mul_zero]

theorem AtIdn.rider {D : Dim} {t : Raw → K} (h : AtIdn D t) (C : Calls) (z : ℕ → K) :
    Rider D C z t := rider_of_at3 h.at3 C z

/-- **The sum of the sumcheck for the bits is 0**, for any number kap of variables for the number of
a bit. -/
theorem bitSum_zero (kap : ℕ) {D : Dim} {t : Raw → K} (h : AtIdn D t) (p : Pub K) :
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
theorem score_start {D : Dim} {t : Raw → K} (h : AtIdn D t) (C : Calls) (p : Pub K) :
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

/-- **The sums of the value product, less the accumulator, less th times the denominator, are 0.**
-/
theorem valueProduct_zero {D : Dim} {C : Calls} {p : Pub K} {t : Raw → K} (h : Rider D C p.z t) :
    sumPhi D C p t .s11 + sumPhi D C p t .s12 - rv D C p t .acc - p.th * rv D C p t .zc = 0 := by
  have e := Cb.Pv.Att.valueMean K D C p t
  have s := Cb.Pv.Att.denOut_split D C p.z t
  unfold Rider at h
  rw [h] at s
  have z : rv D C p t .zc = ∑ b ∈ range D.nb, wp D C p.z .w3 b *
      rd2 D (yg D C p.z) (eqT D (yi D C p.z)) (denV t b) := rfl
  rw [e, z]
  linear_combination p.th * s

end H2K5.Honest

#print axioms H2K5.Honest.idnVal_map
#print axioms H2K5.Honest.AtIdn.map
#print axioms H2K5.Honest.atIdn_of_int
#print axioms H2K5.Honest.rider_of_at3
#print axioms H2K5.Honest.AtIdn.rider
#print axioms H2K5.Honest.bitSum_zero
#print axioms H2K5.Honest.score_start
#print axioms H2K5.Honest.valueProduct_zero
