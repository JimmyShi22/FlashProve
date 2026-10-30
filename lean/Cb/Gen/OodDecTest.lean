-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecTest.lean: a small example in list decoding with out-of-domain samples, at a radius not
below half the distance: what Cb/Gen/OodDec.lean says "fails" does fail (shown here on a sub-table
of one row, a row that stands in two tables (the rule: `Blocks.dec_row_eq`)).

Definitions, statements (in `Cb.Spec`) and their proofs, in one file.

The example, over any field E. The repetition code of length 4 (one coordinate; the codeword of v is
(v, v, v, v); distance 4), at the radius 2: so 2 e = d, the first radius that is not one of unique
decoding, and e < d.
A table of two rows: row "false" = (0, 0, 1, 1), row "true" = (0, 0, 0, 1). Its columns are (0,0),
(0,0), (1,0), (1,1).

Main names:
  `ood_test_dist`: the code has distance at least 4 (`HasDist`).
  `ood_test_table`: the table decodes, at the radius 2, to exactly one table of messages: (0, 0).
  `ood_test_row`: its first row alone decodes, at the radius 2, to exactly two messages: 0 and 1.
  `ood_test_other`: with a sample that has no bad seed at all (`Zid`: err = 0): if the answer 1
    is given for the first row, the decoder with samples (`decS`) returns the message 1 for it,
    which is not the part of the table's only message: the rule "the decoded message of a
    sub-table is the part of the decoded message of the table" (`Blocks.dec_comp`) has no
    counterpart (what remains, under its own hypotheses: `ood_decS_comp`, Cb/Gen/OodDec.lean).
    So a derived table needs its own constraint, and the constraint has to be tied to the first
    table's by the protocol.


Limits: the example is at 2 e = d. It says nothing on how likely such tables are, and nothing on any
protocol.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDecProofs

set_option autoImplicit false

namespace Cb.Ood.Test
open Prob Blocks

/-- the repetition code of length 4 -/
def G (E : Type) [Field E] : Matrix (Fin 4) Unit E := fun _ _ => 1

/-- the table -/
def tf (E : Type) [Field E] : Bool → Fin 4 → E
  | false, j => if 2 ≤ j.val then 1 else 0
  | true, j => if j.val = 3 then 1 else 0

/-- the sample that reads the one entry of a message of one row: one seed, one answer, no bad
seed -/
@[reducible] def Zid (E : Type) [Field E] : Sample E (Unit × Unit) :=
  { D := Unit, S := Unit, mat := fun _ _ _ => 1, err := 0 }

end Cb.Ood.Test

namespace Cb.Spec
open Prob Blocks Cb.Ood Cb.Ood.Test

def ood_test_dist : Prop := ∀ (E : Type) [Field E], HasDist (G E) 4

def ood_test_table : Prop :=
  ∀ (E : Type) [Field E] (M : Bool → Unit → E), DecodesTo (G E) 2 (tf E) M ↔ M = 0

def ood_test_row : Prop :=
  ∀ (E : Type) [Field E] (M : Unit → Unit → E),
    DecodesTo (G E) 2 (fun _ : Unit => tf E false) M ↔ M () () = 0 ∨ M () () = 1

def ood_test_other : Prop :=
  ∀ (E : Type) [Field E],
    (Zid E).OK ∧
    decS (G E) 2 whole (Zid E) (fun _ : Unit => tf E false) () (fun _ => 1) =
      .one (whole fun _ _ => 1)

end Cb.Spec

namespace Cb
open Prob Blocks Cb.Ood Cb.Ood.Test

namespace Ood.Test
variable {E : Type} [Field E]

theorem mulVec_G (v : Unit → E) (j : Fin 4) : (G E).mulVec v j = v () := by
  simp [Matrix.mulVec, dotProduct, G]

theorem f00 : tf E false 0 = 0 := by
  show (if 2 ≤ ((0 : Fin 4) : ℕ) then (1 : E) else 0) = 0
  exact if_neg (by decide)
theorem f01 : tf E false 1 = 0 := by
  show (if 2 ≤ ((1 : Fin 4) : ℕ) then (1 : E) else 0) = 0
  exact if_neg (by decide)
theorem f02 : tf E false 2 = 1 := by
  show (if 2 ≤ ((2 : Fin 4) : ℕ) then (1 : E) else 0) = 1
  exact if_pos (by decide)
theorem f03 : tf E false 3 = 1 := by
  show (if 2 ≤ ((3 : Fin 4) : ℕ) then (1 : E) else 0) = 1
  exact if_pos (by decide)
theorem f10 : tf E true 0 = 0 := by
  show (if ((0 : Fin 4) : ℕ) = 3 then (1 : E) else 0) = 0
  exact if_neg (by decide)
theorem f11 : tf E true 1 = 0 := by
  show (if ((1 : Fin 4) : ℕ) = 3 then (1 : E) else 0) = 0
  exact if_neg (by decide)
theorem f12 : tf E true 2 = 0 := by
  show (if ((2 : Fin 4) : ℕ) = 3 then (1 : E) else 0) = 0
  exact if_neg (by decide)
theorem f13 : tf E true 3 = 1 := by
  show (if ((3 : Fin 4) : ℕ) = 3 then (1 : E) else 0) = 1
  exact if_pos (by decide)

/-- two columns that are not off: at most two are off -/
theorem le_two {P : Fin 4 → Prop} (a b : Fin 4) (hab : a ≠ b) (ha : ¬ P a) (hb : ¬ P b) :
    cnt P ≤ 2 := by
  have h := cnt_add_card_le (P := P) (S := {a, b}) fun j hj => by
    rcases Finset.mem_insert.mp hj with h | h
    · rw [h]; exact ha
    · rw [Finset.mem_singleton.mp h]; exact hb
  rw [Finset.card_pair hab, Fintype.card_fin] at h
  omega

/-- three columns that are off -/
theorem three_le {P : Fin 4 → Prop} (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : P a) (hb : P b) (hc : P c) : 3 ≤ cnt P := by
  have h := card_le_cnt (P := P) {a, b, c} fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h | h <;> rw [h] <;> assumption
  rwa [Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩] at h

end Ood.Test

theorem ood_test_dist : Spec.ood_test_dist := by
  intro E _ v hv
  have h0 : v () ≠ 0 := fun h => hv (funext fun _ => h)
  have h := card_le_cnt (P := fun j => (G E).mulVec v j ≠ 0) Finset.univ fun j _ => by
    show (G E).mulVec v j ≠ 0
    rw [mulVec_G]
    exact h0
  rwa [Finset.card_univ, Fintype.card_fin] at h

theorem ood_test_table : Spec.ood_test_table := by
  intro E _ M
  constructor
  · intro h
    by_contra hne
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
    have ha' : M a () ≠ 0 := fun h0 => ha (funext fun _ => h0)
    have h0 : Off (G E) (tf E) M 0 :=
      ⟨a, by rw [mulVec_G]; cases a <;> simp only [f00, f10] <;> exact fun h => ha' h.symm⟩
    have h1 : Off (G E) (tf E) M 1 :=
      ⟨a, by rw [mulVec_G]; cases a <;> simp only [f01, f11] <;> exact fun h => ha' h.symm⟩
    have h3 : 3 ≤ cnt (Off (G E) (tf E) M) := by
      by_cases h2 : Off (G E) (tf E) M 2
      · exact three_le 0 1 2 (by decide) (by decide) (by decide) h0 h1 h2
      · have h2' := not_off_iff.mp h2 true
        rw [mulVec_G, f12] at h2'
        refine three_le 0 1 3 (by decide) (by decide) (by decide) h0 h1 ⟨true, ?_⟩
        rw [mulVec_G, f13, ← h2']
        exact one_ne_zero
    have h' : cnt (Off (G E) (tf E) M) ≤ 2 := h
    omega
  · rintro rfl
    refine le_two 0 1 (by decide) (not_off_iff.mpr fun a => ?_) (not_off_iff.mpr fun a => ?_)
    · rw [mulVec_G]; cases a <;> simp only [f00, f10] <;> rfl
    · rw [mulVec_G]; cases a <;> simp only [f01, f11] <;> rfl

theorem ood_test_row : Spec.ood_test_row := by
  intro E _ M
  constructor
  · intro h
    by_contra hne
    rw [not_or] at hne
    have hoff : ∀ j, tf E false j = 0 ∨ tf E false j = 1 →
        Off (G E) (fun _ : Unit => tf E false) M j := fun j hj =>
      ⟨(), by
        rw [mulVec_G]
        show tf E false j ≠ M () ()
        rcases hj with hj | hj <;> rw [hj]
        · exact fun h => hne.1 h.symm
        · exact fun h => hne.2 h.symm⟩
    have h3 := three_le (P := Off (G E) (fun _ : Unit => tf E false) M) 0 1 2 (by decide)
      (by decide) (by decide) (hoff 0 (Or.inl f00)) (hoff 1 (Or.inl f01)) (hoff 2 (Or.inr f02))
    have h' : cnt (Off (G E) (fun _ : Unit => tf E false) M) ≤ 2 := h
    omega
  · rintro (h | h)
    · refine le_two 0 1 (by decide) (not_off_iff.mpr fun a => ?_) (not_off_iff.mpr fun a => ?_)
      · rw [mulVec_G, f00, h]
      · rw [mulVec_G, f01, h]
    · refine le_two 2 3 (by decide) (not_off_iff.mpr fun a => ?_) (not_off_iff.mpr fun a => ?_)
      · rw [mulVec_G, f02, h]
      · rw [mulVec_G, f03, h]

theorem ood_test_other : Spec.ood_test_other := by
  intro E _
  have hval : ∀ u : Unit × Unit → E, (Zid E).val () u () = u ((), ()) := fun u => by
    show ∑ n : Unit × Unit, (1 : E) * u n = u ((), ())
    rw [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique, one_mul]
  refine ⟨fun v hv => le_of_eq (cnt_false fun ρ hρ => hv (funext fun n => ?_)), ?_⟩
  · have h := (hval v).symm.trans (congrFun hρ ())
    exact h
  · refine (ood_decS_iff E (Fin 4) Unit Unit (Unit × Unit) (G E) 2 whole (Zid E) _ () _ _).mpr
      ⟨⟨_, (ood_test_row E _).mpr (Or.inr rfl), rfl⟩,
        funext fun _ => hval _,
        fun M' _ h2 => funext fun n => ?_⟩
    exact (hval (whole M')).symm.trans (congrFun h2 ())

end Cb
