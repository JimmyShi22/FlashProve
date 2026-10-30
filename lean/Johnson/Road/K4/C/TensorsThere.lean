-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TensorsThere.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4): every tensor of the verifier's list is
found with the tables of its matrix, and its entries (at the token point) or its blocks (at the
lookup's point) are there, at every layer of the tensor: the hypotheses Short and Long
(ReadersReturn.lean), for all the library's arrays at once. The verifier's cell is the library's
feature (the library's ten_of, place_eq_feat, Johnson/Road/FormsKeysFits.lean); a valid name's
feature lies inside its matrix's parts (valid_inMat, ValidIn.lean); a family of tables has an entry
for each (Reach, from ReachPlan.lean). Statements and proofs.

  `fc_blocks`       a column of a matrix with long tables holds whole blocks.
  **`short_of_arr`**  Short at an array of the matrices ad, ar.
  **`long_of_arr`**   Long at an array of the matrices af, qa.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. UNDER THE
LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. Public data alone: whether a form IS THERE, nothing
on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.ReachPlan
import Johnson.Road.K4.C.ValidIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay)
open Inst.Model.FFSeg (Dim Arr Cell)

variable {v : Env} {D : Dim}

/-- A column of a matrix with long tables holds whole blocks: as many as it has runs of 2 ^ la
rows. -/
theorem fc_blocks {y : Lay} (L : Laid y) (L2 : Laid2 y) (hla : y.h.la = y.ls + y.h.lt) {mat : ℕ}
    (hm : mat ∈ [0, 3, 4, 5]) : fcM y mat = rowsM y mat / 2 ^ y.h.la * y.S2 := by
  obtain ⟨lm, hle, hrow⟩ := rows_of_laid2 L2 mat hm
  unfold fcM
  rw [hrow, L2.T, L.S2, Nat.pow_div hle (by norm_num), Nat.pow_div (by omega) (by norm_num),
    ← Nat.pow_add]
  congr 1
  omega

/-- **An array of the matrices ad, ar: its tensor is found with its tables at the lookup's token
point, and all entries of each of its layers are there.** -/
theorem short_of_arr (L : Laid v.y) (L2 : Laid2 v.y) (S : Switches v.y.h) (Z : Sized v.y.h D)
    (hp4 : v.y.h.p4 = true) (X : Arr) (hX : inList v.y.h X)
    (R : ∃ tb, v.tabAt (Env.mname (matNo X) ++ "@" ++ "zt") = some tb ∧
      Reach v tb (partsM v.y (matNo X) * (colsM v.y (matNo X) * (rowsM v.y (matNo X) / v.y.T))))
    {i : ℕ} (hi : i < X.cnt D) : Short v (arrName X) "zt" i (X.width D) := by
  obtain ⟨ten, hT, hm, hnl, -, -, -⟩ := ten_of L S X hX
  obtain ⟨tb, htb, R⟩ := R
  refine ⟨ten, tb, ?_, fun j hj => shortA_some R fun l hl => ?_⟩
  · unfold Env.tensorAt
    rw [hT]
    show (v.tabAt (Env.mname ten.mat ++ "@" ++ "zt") >>= fun tb => pure (ten, tb)) = _
    rw [hm, htb]
    rfl
  · rw [(place_eq_feat L S Z X hX hT l i j).1]
    have hv : (⟨X, l, i, j, 0⟩ : Cell).Valid D :=
      ⟨hnl ▸ hl, hi, hj, Inst.Model.FFSeg.IndexFacts.T_pos D⟩
    obtain ⟨-, hlt⟩ := valid_inMat L2 S Z hp4 hv
    rw [← matNo_eq, Nat.mul_assoc] at hlt
    exact hlt

/-- **An array of the matrices af, qa: its tensor is found with its long tables at the lookup's
point, and all blocks of each of its layers are there.** -/
theorem long_of_arr (L : Laid v.y) (L2 : Laid2 v.y) (S : Switches v.y.h) (Z : Sized v.y.h D)
    (hp4 : v.y.h.p4 = true) (hla : v.y.h.la = v.y.ls + v.y.h.lt) (X : Arr)
    (hX : inList v.y.h X) (hm03 : matNo X = 0 ∨ matNo X = 3)
    (R : ∃ tb, v.tabAt (Env.mname (matNo X) ++ "@" ++ "Z") = some tb ∧
      Reach v tb
        (partsM v.y (matNo X) * (colsM v.y (matNo X) * (rowsM v.y (matNo X) / 2 ^ v.y.h.la))))
    {i : ℕ} (hi : i < X.cnt D) : Long v (arrName X) i (X.width D / v.y.S2) := by
  obtain ⟨ten, hT, hm, hnl, -, -, -⟩ := ten_of L S X hX
  obtain ⟨tb, htb, R⟩ := R
  have hS2 : 0 < v.y.S2 := by
    rw [L.S2]
    exact Nat.two_pow_pos _
  have hfc : fcM v.y (matNo X) = rowsM v.y (matNo X) / 2 ^ v.y.h.la * v.y.S2 :=
    fc_blocks L L2 hla (by rcases hm03 with e | e <;> rw [e] <;> simp)
  refine ⟨ten, tb, ?_, fun jh hj => longA_some R fun l hl => ?_⟩
  · unfold Env.tensorAt
    rw [hT]
    show (v.tabAt (Env.mname ten.mat ++ "@" ++ "Z") >>= fun tb => pure (ten, tb)) = _
    rw [hm, htb]
    rfl
  · have hjw : jh * v.y.S2 < X.width D := by
      have h1 := (Nat.le_div_iff_mul_le hS2).mp (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at h1
      omega
    have hv : (⟨X, l, i, jh * v.y.S2, 0⟩ : Cell).Valid D :=
      ⟨hnl ▸ hl, hi, hjw, Inst.Model.FFSeg.IndexFacts.T_pos D⟩
    obtain ⟨-, hlt⟩ := valid_inMat L2 S Z hp4 hv
    rw [← (place_eq_feat L S Z X hX hT l i (jh * v.y.S2)).1, ← matNo_eq, hfc] at hlt
    have e0 : tenCell ten.place l i (jh * v.y.S2) = tenCell ten.place l i 0 + jh * v.y.S2 := rfl
    rw [e0] at hlt
    have e1 : (tenCell ten.place l i 0 + jh * v.y.S2) / v.y.S2 =
        tenCell ten.place l i 0 / v.y.S2 + jh := Nat.add_mul_div_right _ _ hS2
    rw [← e1]
    apply Nat.div_lt_of_lt_mul
    calc tenCell ten.place l i 0 + jh * v.y.S2
        < partsM v.y (matNo X) * colsM v.y (matNo X) *
            (rowsM v.y (matNo X) / 2 ^ v.y.h.la * v.y.S2) := hlt
      _ = v.y.S2 * (partsM v.y (matNo X) *
            (colsM v.y (matNo X) * (rowsM v.y (matNo X) / 2 ^ v.y.h.la))) := by ring

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.fc_blocks
#print axioms OnBytes.Road.K4.C.short_of_arr
#print axioms OnBytes.Road.K4.C.long_of_arr
