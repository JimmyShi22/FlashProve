-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SquaresSays.lean: what the third claim of group 2 of the layers' own rounds says, as
one extension at the product layer's own point.

  `squares_says`: in a world in which the reads at the last coordinates of the squares' product
      layer's point are true: if every form of K4's group 2 is worth 0, the layer's hidden end value
      is the multilinear extension, at the layer's whole point, of the vector on (norm | feature |
      position) that holds the limbs of the library's stream batched under the powers gp, and 0 at a
      padded norm or feature (`sqV`, Johnson/Road/K4/SquaresPoint.lean).

Limits. An identity in a world, at one point: no draw, no soundness, nothing from the field to the
integers. Fits and TrueAt3 are premises; nothing here shows that they can hold at the layout of a
shipped example. Five public conditions on the layout's numbers are premises too.

-/
import Johnson.Road.K4.Says
import Johnson.Road.K4.SquaresPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell bS)
open Blocks (ext)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  [scl : Scl] {D : Dim} {low u uP uR lowE uE : ℕ → K}

theorem squares_says (F : Fits ρ W v D c t low u) {P : Pub} (hy : P.y = v.y) {H : Heard}
    (T3 : TrueAt3 ρ W v D.lT c (fun j => pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j))
      (fun j => pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j)) uP uR lowE uE)
    (hNI : v.y.NI = D.nNu) (hPd : v.y.Pd = 2 ^ v.y.lPd) (hls : v.y.ls ≤ v.y.lPd)
    (hN : v.y.NI ≤ 2 ^ P.rd.lNI) (hB : v.y.h.d / v.y.S2 ≤ 2 ^ (v.y.lPd - v.y.ls))
    {l : List Aff} (h : Desc.First.K4.normsForms P v H = some l)
    (hz : ∀ f ∈ l, f.value ρ W = 0) :
    W.slot H.wpl.sL =
      ext (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + D.lT)
        (sqV v.y.NI (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) v.y.lPd v.y.xb.nl D.lT
          (fun l => ρ.val (H.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
        (pt ρ H.wpl.r) := by
  obtain ⟨_, _, e, he, hs⟩ := norms_says F T3 hy hNI h hz
  have he' : hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls) = .ok e := by
    cases hh : hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls) with
    | ok a =>
      rw [hh] at he
      have : a = e := by simpa [Except.toOption] using he
      rw [this]
    | error s =>
      rw [hh] at he
      simp [Except.toOption] at he
  rw [hs, ← squares_point ρ hls he' hN hB]
  simp only [hPd, F.S2]

#print axioms squares_says

end OnBytes.Road.K4
