-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Plan/FilledOf.lean: THE LAYERS' LAYOUT's NUMBERS OF FILLED FEATURES, AND SIX
INEQUALITIES BETWEEN THEM AND THE SIZES OF THE MATRICES: wherever Layer.layout
(OnBytes/Model/LayerLayout.lean) returns. General: no scope, no numeral.

Why. The planned length of a layers' sub-proof's vector of reads (Reads.nW) is written with the
filled features; the tables that are laid in that vector are sized by the matrices' rows and
columns. These six inequalities say, matrix by matrix, that one table's entries are at most what nW
counts for it.

  `Filled y`: two lines of layoutBase that `Laid2` (Johnson/Road/FormsKeysAddr.lean) does
    not hold: y.filled and y.xbFilled as the text writes them. `filled_of_base`, `filled_of_layout`.
    `Filled.filled0` … `filled3`: member by member.
  `short_le`, `short_one`, `long_le`, `long_one`: the arithmetic: with u = na * c: na parts of F / u
    columns and c features each hold at most F features; the like for blocks of 2 ^ la rows.
  **`af_long`**, **`qa_long`**, **`xb_long`**: a long table (one entry a column and a block of 2 ^
    la rows).
  **`ad_short`**, **`ar_short`**, **`qa_short`**: a short table (one entry a column and a feature).
The opening of layoutBase's text is that of `laid2_of_base`, line for line.
Limits. That the layout returns anywhere is not said. Nothing on the matrix b (its table has kbm
entries by the text). Nothing on soundness.

-/
import Johnson.Road.FormsKeysAddr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Plan

open OnBytes.Model (refuseIf roundUp)
open OnBytes.Model.Layer (Lay Shape layout layoutBase layoutLook)
open OnBytes.Road (ok_of_bind ok_of_refuse look_keeps Laid2 offsOf sizesOf sizesOf_eq)

/-- Two more lines of layoutBase: the features with the fill. -/
structure Filled (y : Lay) : Prop where
  /-- of the four matrices af, ad, ar, qa -/
  filled : y.filled = ((sizesOf y.h).map (·.2.1)).toArray
  /-- of a matrix of the residual stream -/
  xb : y.xbFilled = roundUp (y.h.xl * y.h.d) (2 ^ y.h.lmx / 2 ^ y.h.lt)

/-- The first half of the layout. -/
theorem filled_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : Filled y := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  exact ⟨rfl, rfl⟩

/-- The second half of the layout turns neither field. -/
theorem filled_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : Filled y := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have L := filled_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact ⟨L.filled, L.xb⟩

namespace Filled

variable {y : Lay} (F : Filled y)
include F

/-- The filled features of af. -/
theorem filled0 : y.filled.getD 0 0 =
    roundUp ((offsOf y.h).getD 0 0) (y.h.NAf * (2 ^ y.h.lmaf / 2 ^ y.h.lt)) := by
  rw [F.filled, sizesOf_eq]; rfl
/-- Of ad. -/
theorem filled1 : y.filled.getD 1 0 =
    roundUp ((offsOf y.h).getD 1 0) (y.h.NAd * (2 ^ y.h.lmad / 2 ^ y.h.lt)) := by
  rw [F.filled, sizesOf_eq]; rfl
/-- Of ar. -/
theorem filled2 : y.filled.getD 2 0 =
    roundUp ((offsOf y.h).getD 2 0) (1 * (2 ^ y.h.lmar / 2 ^ y.h.lt)) := by
  rw [F.filled, sizesOf_eq]; rfl
/-- Of qa. -/
theorem filled3 : y.filled.getD 3 0 =
    roundUp ((offsOf y.h).getD 3 0) (1 * (2 ^ y.h.lmq / 2 ^ y.h.lt)) := by
  rw [F.filled, sizesOf_eq]; rfl

end Filled

/-! ## The arithmetic -/

/-- na parts of F / u columns, c features a column: at most F features. -/
theorem short_le {F na u c : ℕ} (hu : u = na * c) : na * (F / u * c) ≤ F := by
  calc na * (F / u * c) = F / u * (na * c) := by ring
    _ = F / u * u := by rw [← hu]
    _ ≤ F := Nat.div_mul_le_self F u

/-- One part. -/
theorem short_one {F u c : ℕ} (hu : u = c) : F / u * c ≤ F := by
  subst hu
  exact Nat.div_mul_le_self F u

/-- The like for blocks of 2 ^ la rows, where a column has 2 ^ lm rows and there are 2 ^ lt
positions.
-/
theorem long_le {F na u lm lt la : ℕ} (hu : u = na * (2 ^ lm / 2 ^ lt)) (h1 : lt ≤ lm)
    (h2 : la ≤ lm) : na * (F / u * (2 ^ lm / 2 ^ la)) ≤ F * 2 ^ lt / 2 ^ la := by
  have e1 : 2 ^ lm / 2 ^ la * 2 ^ la = 2 ^ lm := Nat.div_mul_cancel (pow_dvd_pow 2 h2)
  have e2 : 2 ^ lm / 2 ^ lt * 2 ^ lt = 2 ^ lm := Nat.div_mul_cancel (pow_dvd_pow 2 h1)
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos la)]
  calc na * (F / u * (2 ^ lm / 2 ^ la)) * 2 ^ la
      = na * (F / u) * (2 ^ lm / 2 ^ la * 2 ^ la) := by ring
    _ = na * (F / u) * (2 ^ lm / 2 ^ lt * 2 ^ lt) := by rw [e1, e2]
    _ = F / u * (na * (2 ^ lm / 2 ^ lt)) * 2 ^ lt := by ring
    _ = F / u * u * 2 ^ lt := by rw [← hu]
    _ ≤ F * 2 ^ lt := Nat.mul_le_mul_right _ (Nat.div_mul_le_self F u)

/-- One part. -/
theorem long_one {F u lm lt la : ℕ} (hu : u = 2 ^ lm / 2 ^ lt) (h1 : lt ≤ lm) (h2 : la ≤ lm) :
    F / u * (2 ^ lm / 2 ^ la) ≤ F * 2 ^ lt / 2 ^ la := by
  have h := long_le (F := F) (na := 1) (u := u) (by rw [hu, Nat.one_mul]) h1 h2
  rwa [Nat.one_mul] at h

/-! ## The six inequalities -/

section Six

variable {y : Lay} (L : Laid2 y) (F : Filled y)
include L F

/-- **A long table of af, all parts together.** -/
theorem af_long : y.parts.getD 0 0 * (y.kcol.getD 0 0 * (y.mrow.getD 0 0 / 2 ^ y.h.la)) ≤
    y.filled.getD 0 0 * y.T / 2 ^ y.h.la := by
  rw [L.parts0, L.kcol0, L.mrow0, F.filled0, L.T]
  exact long_le rfl L.lt_af L.la_af

/-- **A long table of qa.** -/
theorem qa_long : y.kcol.getD 3 0 * (y.mrow.getD 3 0 / 2 ^ y.h.la) ≤
    y.filled.getD 3 0 * y.T / 2 ^ y.h.la := by
  rw [L.kcol3, L.mrow3, F.filled3, L.T]
  exact long_one (Nat.one_mul _) L.lt_q L.la_q

/-- **A long table of a matrix of the stream.** -/
theorem xb_long : y.kxb * (y.mxb / 2 ^ y.h.la) ≤ y.xbFilled * y.T / 2 ^ y.h.la := by
  rw [L.kxb, L.mxb, F.xb, L.T]
  exact long_one rfl (Nat.le_trans (Nat.le_of_lt L.lt_la) L.la_x) L.la_x

/-- **A short table of ad, all parts together.** -/
theorem ad_short : y.parts.getD 1 0 * (y.kcol.getD 1 0 * (y.mrow.getD 1 0 / y.T)) ≤
    y.filled.getD 1 0 := by
  rw [L.parts1, L.kcol1, L.mrow1, F.filled1, L.T]
  exact short_le rfl

/-- **A short table of ar.** -/
theorem ar_short : y.kcol.getD 2 0 * (y.mrow.getD 2 0 / y.T) ≤ y.filled.getD 2 0 := by
  rw [L.kcol2, L.mrow2, F.filled2, L.T]
  exact short_one (Nat.one_mul _)

/-- **A short table of qa.** -/
theorem qa_short : y.kcol.getD 3 0 * (y.mrow.getD 3 0 / y.T) ≤ y.filled.getD 3 0 := by
  rw [L.kcol3, L.mrow3, F.filled3, L.T]
  exact short_one (Nat.one_mul _)

end Six

end OnBytes.Road.K4.Plan

#print axioms OnBytes.Road.K4.Plan.filled_of_base
#print axioms OnBytes.Road.K4.Plan.filled_of_layout
#print axioms OnBytes.Road.K4.Plan.Filled.filled0
#print axioms OnBytes.Road.K4.Plan.Filled.filled1
#print axioms OnBytes.Road.K4.Plan.Filled.filled2
#print axioms OnBytes.Road.K4.Plan.Filled.filled3
#print axioms OnBytes.Road.K4.Plan.short_le
#print axioms OnBytes.Road.K4.Plan.short_one
#print axioms OnBytes.Road.K4.Plan.long_le
#print axioms OnBytes.Road.K4.Plan.long_one
#print axioms OnBytes.Road.K4.Plan.af_long
#print axioms OnBytes.Road.K4.Plan.qa_long
#print axioms OnBytes.Road.K4.Plan.xb_long
#print axioms OnBytes.Road.K4.Plan.ad_short
#print axioms OnBytes.Road.K4.Plan.ar_short
#print axioms OnBytes.Road.K4.Plan.qa_short
