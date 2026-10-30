-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttMet.lean

"AttOrd", "AttFit" and all hypotheses of "linkA_of_ord" (Johnson/Road/Lane5AttLink.lean) have a
value together: at every lawful table of scales and every group g < 12.

* "shapeAt sh": a record with the reference numbers, four layers with the shift sh, one part of "as"
  with 7,200 columns, and as its table of exponentials the library's refExp at the 2,307 rows. It is
  typed here; it is not shown to be what the verifier's function shape returns (a run says of the
  full-size example that shape returns these numbers and this table: the guards of
  Johnson/Road/Lane5AttWit.lean).
* "attOrd_met": some list Z meets AttOrd (shapeAt sh) Z, with all other hypotheses of linkA_of_ord.
  The list is read out of the matrices of the library's honest trace of a true request
  ("premise_met", Johnson/Road/Lane5Plain.lean: all weights and tokens 0).

It shows "not empty" and no more.
-/
import Johnson.Road.Lane5AttBack
import Johnson.Road.Lane5AttWit
import Johnson.Road.Lane5Plain

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (tbRef refExp)

/-- The library's table of exponentials, as an array of 2,307 numbers. -/
def ttRef : Array ℕ := Array.ofFn (n := 2307) fun i => (refExp ((i : ℕ) : ℤ)).toNat

theorem ttRef_at {ι : ℕ} (h : ι < 2307) : ttRef.getD ι 0 = (refExp (ι : ℤ)).toNat := by
  simp [ttRef, h]

/- from here on the array is a letter: no step may unfold its 2,307 entries -/
attribute [local irreducible] ttRef

/-- A record with the reference numbers, the shift sh in four layers and the library's table. -/
def shapeAt (sh : ℕ) : Attention.Shape :=
  { shapeRef with
    cf := { shapeRef.cf with sh := #[sh, sh, sh, sh], NAs := 1 }, kAs := 7200, Tt := ttRef }

theorem sized_at (sh : ℕ) : AttSized (shapeAt sh) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wide_at (sh : ℕ) :
    7200 ≤ (shapeAt sh).kAs / (shapeAt sh).cf.NAs * (shapeAt sh).cf.NAs := by
  show 7200 ≤ 7200 / 1 * 1
  norm_num

theorem one_at (sh : ℕ) : OneShift (shapeAt sh) := by
  intro l hl
  have hl' : l < 4 := hl
  interval_cases l <;> rfl

theorem fit_at (sh : ℕ) : AttFit (shapeAt sh) := ⟨one_at sh, rfl⟩

theorem exp_at (sh : ℕ) (ι : ℕ) (hι : ι < (shapeAt sh).u0) :
    (((shapeAt sh).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι := by
  have hι' : ι < 2307 := hι
  have e0 : (shapeAt sh).Tt = ttRef := rfl
  rw [e0, ttRef_at hι']
  exact Int.toNat_of_nonneg (le_trans (by norm_num) (le_max_left 1 _))

/-- **AttOrd and the other hypotheses of linkA_of_ord have a value together.** -/
theorem attOrd_met {s : Cm.Scales} (hs : s.Lawful) {g : ℕ} (hg : g < 12) :
    ∃ (S : Attention.Shape) (Z : Zs), AttSized S ∧ AttFit S ∧
      (s.kap (4 * g)).sh = S.cf.sh.getD 0 0 ∧
      (∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) ∧ AttOrd S Z := by
  obtain ⟨i, x, A, _, _, P⟩ := premise_met hs
  exact ⟨shapeAt (s.kap (4 * g)).sh, _, sized_at _, fit_at _, rfl, exp_at _,
    ord_of_premise hg (sized_at _) (wide_at _) rfl (exp_at _) P⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attOrd_met
