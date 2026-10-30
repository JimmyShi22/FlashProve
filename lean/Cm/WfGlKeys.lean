-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/WfGlKeys.lean: the keys of the model's index over p = 2^64 - 2^32 + 1, at the reference numbers:
two lookups of 2^40 keys.

A key is an affine function of one column of the matrix (`Keys.key`, Cb/Gen/WfKeys.lean); the lookup
asks that it is an entry of a fixed table.

Definitions, statements (in `Cm.WfGl.Spec`) and proofs, by instantiating generic sources:
Blocks/RngPlan.lean (`Plan.ofPairs`, `Plan.ofPairs_valid`: any field of characteristic p, under
decidable conditions on numbers), Inst/Model/LayoutBridge.lean (the numbered pairs of rows of the
model's layout), Cb/Gen/WfKeys.lean (`Keys.describes_of_valid`). No weights are in sight: every
statement is for all matrices.

Main names:
  `planGl`: the look-up plan for the model's layout over `Gl.F` with 40 key variables: one key for
    every entry (a signed byte, shifted by 128: table of 2^8) and one for every two-byte weight (low
    + 256 high, shifted by 4096: table of 2^13).
  `WFGl`: the predicate on matrices over `Gl.F`: every entry on the 3,076,096 rows and 2^18 columns
    is a signed byte, and low + 256 high lies in [-2^12, 2^12) in every column of each of the
    1,527,800 numbered pairs of rows (`Blocks.Rng.WFPairs`).
  `keysGl`: its keys (Cb/Gen/WfKeys.lean), with the numbers as numerals: 3,076,096 rows, 18 column
    variables, 22 row variables, two tables: table 0 of 2^8 entries (one key map for all rows of the
    index), table 1 of 2^13 (one for all pairs of rows); offsets and coefficients are the plan's. A
    row of keys beyond the last row (pair) has offset 0 and no coefficient: its keys are 0, an entry
    of the table.
  `Spec.keysGl_eq`: `keysGl` is `Keys.ofPlan planGl`.
  `Spec.planGl_valid`: the plan is valid at `Gl.p` for `WFGl`.
  `Spec.keysGl_describes`: for every matrix over `Gl.F`: `WFGl` holds of it ⇔ every key of both
    tables lies in its table.
  `Spec.keysGl_fits`: the lookup's conditions on numbers, with the width w of a multiplicity as a
    parameter: 41 ≤ w ≤ 50 ⇒ keysGl.Fits Gl.p w (2^40 < 2^w; 2^13 (2^w - 1) < p). `keysGl_fits41`:
    the instance w = 41. `Spec.keysGl_fits_iff`: these are all widths that fit.
  `keysGl_vars`, `keysGl_tables`, `keysGl_tabVars`, `keysGl_tabVars_le`: 40 variables of the cube of
    keys; the numbers.

By reading, a write-up of ours (lean/CREDITS.md) sets its own format against the format of an
implementation: two lookups. The same predicate on matrices.

Limits: this file says nothing on any protocol, code or message. By the same reading
the write-up prints no width of a multiplicity. The plan's two further numbers
(here 40 and 5), which the look-up argument of Blocks/ reads, are carried and not used by
`keysGl`: only the clauses `B_le`, `pl2`, `pl2'` of `Spec.planGl_valid` read them.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gen.WfKeys
import Cb.Gl.GlField
import Inst.Model.LayoutBridge

set_option autoImplicit false

namespace Cm.WfGl
open Blocks Blocks.Rng Cb Inst.Model Inst.Model.Layout

/-- The plan. -/
def planGl : Plan Gl.F :=
  Plan.ofPairs Gl.F hRef kRef 40 40 5 (m2 kRef (units ppref))
    (Bridge.y0 ppref kRef) (Bridge.y1 ppref kRef)

/-- Well formed, over `Gl.F`. -/
def WFGl : (ℕ → ℕ → Gl.F) → Prop :=
  WFPairs hRef kRef (m2 kRef (units ppref)) (Bridge.y0 ppref kRef) (Bridge.y1 ppref kRef)

/-- The keys. -/
def keysGl : Keys Gl.F :=
  ⟨3076096, 18, 22, 2, fun i => if i < 1 then 8 else 13, planGl.off, planGl.Γ⟩

namespace Spec

def keysGl_eq : Prop := keysGl = Keys.ofPlan planGl
def planGl_valid : Prop := planGl.Valid Gl.p WFGl
def keysGl_describes : Prop := keysGl.Describes WFGl
def keysGl_fits : Prop := ∀ w, 41 ≤ w → w ≤ 50 → keysGl.Fits Gl.p w
def keysGl_fits_iff : Prop := ∀ w, keysGl.Fits Gl.p w ↔ 41 ≤ w ∧ w ≤ 50

end Spec

theorem nCallsGl_h : nCalls 40 18 hRef = 1 := by decide

theorem planGl_nc : planGl.nc = 2 := by
  have e : planGl.nc = nCalls 40 kRef hRef + nCalls 40 kRef (m2 kRef (units ppref)) := rfl
  rw [e, Sanity.plan_numbers.1]
  decide

theorem planGl_d : planGl.d = fun i => if i < 1 then 8 else 13 := by
  have e : planGl.d = fun f => if f < nCalls 40 18 hRef then 8 else 13 := rfl
  rw [e, nCallsGl_h]

theorem keysGl_eq : Spec.keysGl_eq := by
  unfold Spec.keysGl_eq keysGl Keys.ofPlan
  rw [planGl_nc, planGl_d]
  rfl

theorem planGl_valid : Spec.planGl_valid := by
  have hh : off kRef (units ppref) (units ppref).length ≤ hRef := by
    rw [Sanity.units_total.1, Sanity.units_total.2]; decide
  exact Plan.ofPairs_valid Gl.p (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (fun q hq => (Bridge.pair_lt ppref kRef hRef hh q hq).1)
    (fun q hq => (Bridge.pair_lt ppref kRef hRef hh q hq).2)

theorem keysGl_describes : Spec.keysGl_describes := by
  unfold Spec.keysGl_describes
  rw [keysGl_eq]
  exact Keys.describes_of_valid (p := Gl.p) planGl_valid

theorem keysGl_vars : keysGl.vars = 40 := rfl
theorem keysGl_tables : keysGl.tables = 2 := rfl
theorem keysGl_tabVars (i : ℕ) : keysGl.tabVars i = if i < 1 then 8 else 13 := rfl

theorem keysGl_tabVars_le (i : ℕ) : keysGl.tabVars i ≤ 13 := by
  rw [keysGl_tabVars]
  split_ifs <;> omega

theorem keysGl_fits : Spec.keysGl_fits := fun w h1 h2 =>
  { pos := by omega
    count := by
      rw [keysGl_vars]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    sum := fun i _ => by
      have h : 2 ^ keysGl.tabVars i ≤ 2 ^ 13 :=
        Nat.pow_le_pow_right (by norm_num) (keysGl_tabVars_le i)
      have hw : 2 ^ w ≤ 2 ^ 50 := Nat.pow_le_pow_right (by norm_num) h2
      calc
        2 ^ keysGl.tabVars i * (2 ^ w - 1) ≤ 2 ^ 13 * (2 ^ 50 - 1) :=
          Nat.mul_le_mul h (Nat.sub_le_sub_right hw 1)
        _ < Gl.p := by decide +kernel }

theorem keysGl_fits41 : keysGl.Fits Gl.p 41 := keysGl_fits 41 (le_refl _) (by norm_num)

theorem keysGl_fits_iff : Spec.keysGl_fits_iff := by
  intro w
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => keysGl_fits w h.1 h.2⟩
  · have h1 := h.count
    rw [keysGl_vars] at h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  · by_contra hc
    have h1 : 2 ^ 13 * (2 ^ w - 1) < Gl.p := h.sum 1 (by decide)
    have hw : 2 ^ 51 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 13 * (2 ^ 51 - 1) ≤ 2 ^ 13 * (2 ^ w - 1) :=
      Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hw 1)
    have h3 : ¬ 2 ^ 13 * (2 ^ 51 - 1) < Gl.p := by decide +kernel
    exact h3 (lt_of_le_of_lt h2 h1)

end Cm.WfGl
