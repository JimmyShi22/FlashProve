-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowCellsAt.lean: CONDITIONAL.

What is here. The verifier's reader of the 99 cells of a norm's row returns at every token point P
at which the family "ar@P" is found with all its entries within the reader's reach (`rowCells_at`):
Johnson/Road/K4/C/RowMapsOf.lean's rowCells_rtV, word for word, with the point a letter. For the
claims on the second token sumcheck's end values, which read the rows at the point rt.

  `rowCells_at`   the cells of row i, for i below the number of norms.

Not shown here. K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES);
that the shape's switch p4 is on (hp4); that the structure has the plan's layout (hy); that the
family is found (htb) and within reach (Rch): hypotheses. Johnson/Road/K4/C/ReachPlan.lean's
reach_family has the last two wherever the family is asked for. THE PROOF IS TYPED TWICE: here and
at rowCells_rtV, which lay first. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Road.K4.C.RowMapsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open Inst.Model.FFSeg (Dim Arr Cell)

variable {Q : K4Pub} {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- **The cells of each norm's row at a token point are made.** CONDITIONAL: on every hypothesis
named. -/
theorem rowCells_at (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true) {v : Env}
    (hy : v.y = Q.P.y) {P : String} {b : ℕ} (htb : v.tabAt ("ar@" ++ P) = some b)
    (Rch : Reach v b (partsM Q.P.y 2 * (colsM Q.P.y 2 * (rowsM Q.P.y 2 / Q.P.y.T)))) {i : ℕ}
    (hi : i < Q.P.y.NI) : ∃ cells, v.rowCells P i 99 = some cells := by
  have Ad := admitted_of_layout A.lay A.sw.p3
  have Sw : Switches Q.P.y.h := by rw [Ad.shape]; exact A.sw
  have h4 : Q.P.y.h.p4 = true := by rw [Ad.shape]; exact hp4
  obtain ⟨trow, hT, -, -, -, hJ, -⟩ := ten_of Ad.laid Sw .D (Or.inl rfl)
  have hJ' : trow.J = 99 := hJ
  have hi' : i < 2 * 2 ^ Q.P.y.h.ll := by
    have e1 := (normsPlan_of_plan A).NI
    have e2 : D.nNu = (dimOf hS).nNu := A.sized.nNu_eq
    rw [e1, e2, ← Ad.shape] at hi
    exact hi
  obtain ⟨cells, hc⟩ := amapM_there (g := fun j => v.U3at b (trow.OFF + i * 99 + j))
    (Array.range 99) (fun j hj => by
      have hj' : j < 99 := by simpa using hj
      show (v.U3at b (trow.OFF + i * 99 + j)).isSome = true
      have e : trow.OFF + i * 99 + j = tenCell trow.place 0 i j := by
        show _ = trow.OFF + (0 * trow.cnt + i) * trow.J + j
        rw [hJ', Nat.zero_mul, Nat.zero_add]
      rw [e, (place_eq_feat Ad.laid Sw (sized_dimOf _) .D (Or.inl rfl) hT 0 _ _).1]
      have hv : (⟨.D, 0, i, j, 0⟩ : Cell).Valid (dimOf Q.P.y.h) :=
        ⟨Nat.zero_lt_one, hi', hj', Inst.Model.FFSeg.IndexFacts.T_pos _⟩
      obtain ⟨-, hlt⟩ := valid_inMat (laid2_of_layout A.lay) Sw (sized_dimOf _) h4 hv
      rw [Nat.mul_assoc] at hlt
      exact Rch _ hlt)
  refine ⟨cells, ?_⟩
  have hT' : Q.P.y.T_ "row" = some trow := hT
  unfold Env.rowCells
  rw [htb, hy, hT']
  exact hc

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rowCells_at
