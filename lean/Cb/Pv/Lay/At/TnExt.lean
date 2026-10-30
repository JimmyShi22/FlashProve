-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/TnExt.lean: the library's values of the tensor claims of a weight panel, as extensions
of the panel's B side at coordinates of the batched sumcheck's end point.

Inst/Model/FF/Objects.lean defines Pan.TnRow (a row of a panel under the equality weights of its
columns) and Pan.TnPan (a panel under those of its rows and columns). The batched sumcheck's second
side is made of pieces, each the extension of a vector at a run of coordinates of the end point
(extAt in Cb/Pv/Lay/At/Place.lean). This file shows that the extension of a row of the B side, cut
to the panel's columns, is TnRow, and that the extension of the whole B side on the panel's cells
(cellOf in Cb/Pv/Lay/At/PanPlace.lean) is TnPan.

Main theorems: row_ext, pan_ext.

Limits. Identities of sums alone.


-/
import Cb.Pv.Lay.At.PanPlace
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At

open Finset
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim Pan Rd LW lamS)
open Blocks (eqN)

variable {E : Type} [Field E] (D : Dim) (r : Rd E) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E)
  (z zh ζ : ℕ → E)

/-- The extension of row ρ of the B side, cut to the panel's columns, is TnRow. -/
theorem row_ext (p : Pan) (ρ : ℕ) :
    extAt (p.wcol D) (lamS D - p.wcol D)
        (fun ι => if ι < p.nc D then p.B D r tb L0 w z zh ρ ι else 0) ζ =
      p.TnRow D r tb L0 w z zh ζ ρ := by
  exact extAt_cut (g := p.wcol D) (n := p.nc D) (off := lamS D - p.wcol D)
    (Nat.le_pow_clog (by norm_num) _) (fun ι => p.B D r tb L0 w z zh ρ ι) ζ

/-- The extension of the B side on the panel's cells is TnPan. -/
theorem pan_ext (p : Pan) (hp : p.wid D ≤ lamS D) :
    extAt (p.wid D) (lamS D - p.wid D) (cellOf D p fun ρ ι => p.B D r tb L0 w z zh ρ ι) ζ =
      p.TnPan D r tb L0 w z zh ζ := by
  have hw : p.wid D = Nat.clog 2 (p.nr D) + p.wcol D := rfl
  unfold extAt
  rw [local_sum D p (fun t => eqN (p.wid D) (lamS D - p.wid D) ζ t)
    fun ρ ι => p.B D r tb L0 w z zh ρ ι]
  unfold Inst.Model.FFSeg.Pan.TnPan Inst.Model.FFSeg.Pan.TnRow
  refine sum_congr rfl fun ρ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun ι hι => ?_
  have hι' : ι < 2 ^ p.wcol D :=
    lt_of_lt_of_le (mem_range.mp hι) (Nat.le_pow_clog (by norm_num) _)
  have e1 : eqN (p.wid D) (lamS D - p.wid D) ζ (ρ * 2 ^ p.wcol D + ι) =
      eqN (Nat.clog 2 (p.nr D)) (lamS D - p.wid D) ζ ρ *
        eqN (p.wcol D) (lamS D - p.wid D + Nat.clog 2 (p.nr D)) ζ ι := by
    rw [hw]
    exact Blocks.eqN_append' _ _ _ ζ ρ hι'
  have e2 : p.Er D ζ ρ = eqN (Nat.clog 2 (p.nr D)) (lamS D - p.wid D) ζ ρ := by
    unfold Inst.Model.FFSeg.Pan.Er
    rw [hw, Nat.add_sub_cancel]
  have e3 : p.Ec D ζ ι = eqN (p.wcol D) (lamS D - p.wid D + Nat.clog 2 (p.nr D)) ζ ι := by
    unfold Inst.Model.FFSeg.Pan.Ec
    congr 1
    omega
  rw [e1, e2, e3]
  ring

end Cb.Pv.Lay.At
