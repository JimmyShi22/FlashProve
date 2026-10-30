-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/StartsAt.lean: CONDITIONAL.

Not shown here. WHAT THE SLOTS UNDER THE NEVER-SENT VECTORS' VALUES ARE WORTH (h1, h2: the fields of
that name of OpenedOwn, Johnson/Road/K4/W/OpenedOwn.lean) AND THOSE UNDER THE NORMS' NINE SUMS (hW:
the field sums of Opened, W/Ground.lean): hypotheses here; Law/W/RightStack.lean and
Law/W/Halves.lean have them under hypotheses of their own. TensorIs; Fits' ties, CellsAre and
NormsPlan; that the limbs are batched under the powers of one element; that the tables and the
squares' job are returned and the first cube's sizes fit; that the sampled values in p are the
verifier's; sizes: hypotheses. That they can hold together: no example is known. The import closure
holds what Law/SumStarts.lean's holds, and Johnson/Road/K4/C/. Nothing on soundness, on completeness
or on any other property. No property is claimed.

The start of a masked sumcheck: the form that the verifier takes as the claimed sum is worth the
reading of the total of the cube of the honest side's job. Here at the two gated products and at the
squares, in the letters in which Law/OwnAtStand.lean asks them (its premises on these three starts):
from what the slots are worth (OpenedOwn's h1, h2), the totals as extensions (`gated_total_ext`,
Law/SumTotalExt.lean; `gated2_sigma`, Law/SumStarts.lean) and the tables' entries (`tabs1_are`,
`tabs2_are`, Johnson/Road/K4/C/GatedTabs.lean); at the squares from `squares_sigma`
(Law/SumStarts.lean), the table's entries (`sqTab_read`, C/NormsTabs.lean) and the library's
`sqV_sqTab` (Johnson/Road/K4/NormsReads.lean).

  `start_gated1`   the first gated product: one slot.
  `start_gated2`   the second: the form start2.
  `start_squares`   the squares: normsStart's form.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumStarts
import Johnson.Road.K4.C.GatedTabs
import Johnson.Road.K4.C.NormsTabs
import Johnson.Road.K4.ClaimsPaid
import Johnson.Road.K4.NormsReads
import OnBytes.Desc.First.K4.BatchLaws
import Johnson.Desc.ProofFile.Honest.K4.Law.SumLevels

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (Reading World Aff Tsc orderRange powers ledNS)
open OnBytes.Model.Layer (Own Ten downFrom normsStart)
open OnBytes.Road (pt eqR Fits Mats cellsAt wHat)
open OnBytes.Road.Rows (start2 hvOf)
open OnBytes.Road.K4 (gl_half)
open OnBytes.Road.K4.C (TensorIs GatedNums tabs1_are tabs2_are CellsAre NormsPlan sqTab_read)
open OnBytes.Desc.First.K4 (powers_val sqV_sqTab)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim Cell lF lFe slV upV)

variable {Q : K4Pub} {w : K4In} {o : Own} {D : Dim} {t : Cell → Cb.Gl.E} {Wd : World Cb.Gl.E}
  {ts tu : Ten}

/-- **THE FIRST GATED PRODUCT's START.** CONDITIONAL: on every hypothesis named. -/
theorem start_gated1
    (h1 : Wd.slot o.K.sH1 = Blocks.ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X)
      (pt Reading.gl (downFrom o.K.rs (D.lL + lF D) ++ o.H.ztF)))
    (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    (hll : Q.P.y.h.ll = D.lL) (hPf : Q.P.y.lPf = lF D) (p : Pts) (hrs : p.rs = o.K.rs)
    (hzt : ztOf Q p = o.H.ztF) {tb : Tab × Tab} (htb : gatedTabs Q w = some tb)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) tb).cube.fits = true) :
    (Aff.slot o.K.sH1).value Reading.gl Wd =
      Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
        (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) tb).cube.total := by
  rw [gated_total_ext Reading.gl Q p tb hfit, Aff.value_slot, h1, N.muH, hrs, hzt, hll, hPf]
  refine Blocks.ext_congr (fun X hX => ?_) _
  obtain ⟨a, b⟩ := tabs1_are hts htu Ss Su N htb hX
  rw [a, b]

/-- **THE SECOND GATED PRODUCT's START.** CONDITIONAL: on every hypothesis named. -/
theorem start_gated2 {tT : Tsc}
    (h2 : ∀ lm, lm < Q.P.y.LamM → Wd.slot (o.K.sH1 + 1 + lm) =
      ∑ yv ∈ Finset.range (2 ^ lFe D), eqR Reading.gl o.K.rs 0 (lFe D) yv *
        hvOf D t (pt Reading.gl o.H.ztF) (pt Reading.gl tT.r) (1 + lm) yv)
    (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D) (p : Pts)
    (hrs : p.rs = o.K.rs) (hrt : p.rt = tT.r) (hle : lFe D ≤ o.K.rs.size)
    (hrho : p.rhoM.size = D.lL - 1) (hsz : tT.r.size = D.lT) {tb : Tab × Tab}
    (htb : gatedTabs2 Q w = some tb) :
    (start2 Q.P.y.LamM o.K.sH1 p.rhoM).value Reading.gl Wd =
      Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
        (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt) tb).cube.total :=
  gated2_sigma (u := pt Reading.gl o.H.ztF) Q.P.rd.muH2 (orderRange Q.P.rd.muH2) tb N.lfe
    (by rw [hrs, N.lfe]; exact hle) hrho (by rw [hrt]; exact hsz) N.LamM N.muH2
    (fun lm hlm => by rw [N.lfe, hrs, hrt]; exact h2 lm hlm)
    (fun X hX => tabs2_are hts htu Ss Su N htb (by rw [← N.muH2]; exact hX))

/-- **THE SQUARES' START.** x: the one element under whose powers the limbs are batched.
CONDITIONAL: on every hypothesis named. -/
theorem start_squares [scl : Scl] {W₀ : World Cb.Gl.E} {Mm : Mats Cb.Gl.E} {low u : ℕ → Cb.Gl.E}
    (F : Fits Reading.gl W₀ o.v D (cellsAt o.v.y Mm) t low u) (hy : Q.P.y = o.v.y)
    (C : CellsAre Q w Mm) (Np : NormsPlan Q D)
    (hW : ∀ ν, ν < D.nNu → ∀ s, s < 9 →
      Wd.slot (o.H.sW + 9 * ν + s) = wHat D t ν (pt Reading.gl o.H.PV) s)
    (p : Pts) (hPV : p.PV = o.H.PV) {x : E} (hgp : p.gp = powers x (ledNS Q.P.y.h.xl))
    (hNS : ledNS Q.P.y.h.xl = 9) (hnl : Q.P.y.xb.nl = 5) (hsz : p.rhoI.size = Q.P.rd.lNI)
    (hPs : o.H.PV.size = D.lT) (hN : D.nNu ≤ 2 ^ Q.P.rd.lNI) (hd : D.d ≤ 2 ^ Q.P.y.lPd) {j : Job}
    (hj : jobSquares Q w p = some j) :
    (normsStart Q.P.y o.H.sW p.gp p.rhoI p.PV).1.value Reading.gl Wd =
      Reading.gl.val j.cube.total := by
  rw [jobSquares_eq] at hj
  split at hj
  · obtain rfl := Option.some.inj hj
    have hg : ∀ s, s < 9 → Reading.gl.val (p.gp.getD s zeroE) = Reading.gl.val x ^ s :=
      fun s hs => by rw [hgp]; exact powers_val Reading.gl x (by rw [hNS]; exact hs)
    have hdd : o.v.y.h.d / o.v.y.S2 * 2 ^ o.v.y.ls = D.d := by
      obtain ⟨n, hn⟩ := F.bd
      rw [F.d, F.S2, hn, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    refine squares_sigma Q.P.y o.H.sW Q.P.rd.muV p.gp p.rhoI p.PV Q.P.rd.lNI (Reading.gl.val x)
      (squaresTab Q w p.gp) hNS Np.NI gl_half hsz (by rw [hPV]; exact hPs)
      (by have h1 := Np.muV; have h2 := Np.lsPd; omega) hN hd hg
      (fun ν hν s hs => by rw [hPV]; exact hW ν hν s hs) (fun X hX => ?_)
    rw [sqTab_read F hy C Np p.gp hX, hdd, ← hy, Np.NI, hnl]
    exact congrFun (sqV_sqTab Q.P.rd.lNI Q.P.y.lPd _ (Reading.gl.val x)
      (fun l hl => hg l (by omega))) X
  · cases hj

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.start_gated1
#print axioms ProofFile.Honest.K4.W.start_gated2
#print axioms ProofFile.Honest.K4.W.start_squares
