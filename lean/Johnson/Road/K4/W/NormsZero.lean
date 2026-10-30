-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/NormsZero.lean: CONDITIONAL.

What is here. Group 2 of the layers' own rounds (sub-protocol K4): each of the three forms of the
list `normsForms` (OnBytes/Desc/First/K4/Claims.lean) has the value 0 (`Aff.value`) in a world in
which the squares' own claim has that value, the product layer's two end values are one, and the
left one is the library's term. It is `norms_says` (Johnson/Road/K4/Says.lean) and `squares_says`
(Johnson/Road/K4/SquaresSays.lean) read from right to left. Statements and proofs.

  **`norms_zero`**    with the left end value as the sum over norms, blocks and limbs.
  **`norms_zero'`**   with the left end value as one extension at the product layer's point.

Not shown here. That any world meets the premises: no example is known. THAT THE TABLES OF THE
READS ARE TRUE OF THE CELLS IN W IS A PREMISE (Fits, Johnson/Road/FormsKeysKit.lean; TrueAt3,
Johnson/Road/FormsKeysTrue3.lean); so are P.y = v.y and NI = nNu, and for `norms_zero'` four more
conditions on the layout's numbers. That the list is there anywhere: both statements start from
its return. OF THE THREE FORMS ONE ALONE COMES BY A LAW: the first, the squares' own claim, is a
premise (hrow); the second says what the premise hLR says; the third comes from the library's
equation (`Fits.normsEnd`, Johnson/Road/FormsKeysIdnL.lean). That a prover's play lays these
values under the slots. ρ, W and the cells are free; so are the points, but that `norms_zero'`
sets lowV and uV at coordinates of the product layer's point.
No property is claimed.
-/
import Johnson.Road.K4.NormsReads
import Johnson.Road.K4.Says
import Johnson.Road.K4.SquaresPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard Pub epsOf twoM)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell idnVal led bS npOf)
open Blocks (ext)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (rowsForms normsForms digitsAt digitsAt_found)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- **GROUP 2**, the left end value as a sum. -/
theorem norms_zero (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) {P : Pub} (hy : P.y = v.y) {H : Heard}
    (hNI : v.y.NI = D.nNu) (hrow : H.wpl.row.value ρ W = 0)
    (hLR : W.slot H.wpl.sR = W.slot H.wpl.sL)
    (hL : ∀ e, (hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls)).toOption = some e →
      W.slot H.wpl.sL =
        ∑ x ∈ range (v.y.NI * (v.y.h.d / v.y.S2) * v.y.xb.nl),
          ρ.val (e.getD (x / v.y.xb.nl / (v.y.h.d / v.y.S2) * v.y.Pd / v.y.S2 +
            x / v.y.xb.nl % (v.y.h.d / v.y.S2)) zeroE) *
              ρ.val (H.gp.getD (x % v.y.xb.nl) zeroE) *
          ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
            ext D.lT (fun p => bS D t (x / v.y.xb.nl / (v.y.h.d / v.y.S2)) (x % v.y.xb.nl)
              (x / v.y.xb.nl % (v.y.h.d / v.y.S2) * 2 ^ v.y.ls + r) p) uV) :
    ∀ l, normsForms P v H = some l → ∀ f ∈ l, f.value ρ W = 0 := by
  intro l h
  obtain ⟨txs, tI, tA, e, sum, a1, a2, a3, a4, a5, rfl⟩ :=
    Desc.First.K4.normsL_shape (Road.K4.normsForms_normsL h)
  rw [hy] at a1 a4 a5
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hrow
  rcases List.mem_cons.mp hf with rfl | hf
  · rw [Aff.value_sub, Aff.value_slot, Aff.value_slot, hLR, sub_self]
  · obtain rfl := List.mem_singleton.mp hf
    exact (F.normsEnd T3 a2 a3 a1 hNI e H.gp H.wpl.sL a5).trans (sub_eq_zero.mpr (hL e a4))

/-- **GROUP 2**, the left end value as one extension at the product layer's point. -/
theorem norms_zero' (F : Fits ρ W v D c t low u) {P : Pub} (hy : P.y = v.y) {H : Heard}
    (T3 : TrueAt3 ρ W v D.lT c (fun j => pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j))
      (fun j => pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j)) uP uR lowE uE)
    (hNI : v.y.NI = D.nNu) (hPd : v.y.Pd = 2 ^ v.y.lPd) (hls : v.y.ls ≤ v.y.lPd)
    (hN : v.y.NI ≤ 2 ^ P.rd.lNI) (hB : v.y.h.d / v.y.S2 ≤ 2 ^ (v.y.lPd - v.y.ls))
    (hrow : H.wpl.row.value ρ W = 0) (hLR : W.slot H.wpl.sR = W.slot H.wpl.sL)
    (hL : W.slot H.wpl.sL =
      ext (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + D.lT)
        (Road.K4.sqV v.y.NI (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) v.y.lPd v.y.xb.nl D.lT
          (fun l => ρ.val (H.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
        (pt ρ H.wpl.r)) :
    ∀ l, normsForms P v H = some l → ∀ f ∈ l, f.value ρ W = 0 := by
  refine norms_zero F T3 hy hNI hrow hLR fun e he => ?_
  have he' : hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls) = .ok e := by
    cases hh : hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls) with
    | ok a =>
      rw [hh] at he
      have : a = e := by simpa [Except.toOption] using he
      rw [this]
    | error s =>
      rw [hh] at he
      simp [Except.toOption] at he
  rw [hL, ← Road.K4.squares_point ρ hls he' hN hB]
  simp only [hPd, F.S2]

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.norms_zero
#print axioms OnBytes.Road.K4.W.norms_zero'
