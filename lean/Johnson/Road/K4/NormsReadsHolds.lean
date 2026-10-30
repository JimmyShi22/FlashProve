-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormsReadsHolds.lean: the norms' stage of the layers' own rounds: the group
`Run.ReadsTrue` of the per-position bridge, from "every table of the reads holds what it says of the
matrices" and public lines of the layout.

K4/NormsReads.lean draws `Run.ReadsTrue` from the library's two records Fits and TrueAt3. The
library concludes both records from one statement on the world, `∀ Fn ∈ funs, Holds ρ W tl iU3 K3 M
Fn` (Johnson/Road/FormsKeysMat.lean: each entry of the reads is the stated sum of entries of the
matrices M), and from lines of the verifier's own layout: trueAt_of_holds, trueAt3_of_holds,
fits_of_layout_true. Here the three are laid in front.

  `longTrue_congr`: a true long table reads the first coordinates of its two points alone.
  `lastOf_pt`: a coordinate of the last k coordinates of a point.
  `readsTrue_of_holds`: the law.

Limits. THAT EVERY TABLE HOLDS IS A PREMISE (the row reads_are_true is another kind's). The public
lines (the layout; the switches; the scales' test; the reads' lists; the tables' places; the sizes
D; seven numbers) are premises: nothing here shows them at the layout of a shipped example. No draw,
no soundness.
-/
import Johnson.Road.K4.NormsReads
import Johnson.Road.FormsKeysAdmit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4
open Finset
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

theorem longTrue_congr {v : Env} {tb mat ls lt : ℕ} {c : Road.Cells K} {low low' u u' : ℕ → K}
    (hl : ∀ j, j < ls → low j = low' j) (hu : ∀ j, j < lt → u j = u' j)
    (h : Road.LongTrue ρ W v tb mat ls lt c low u) :
    Road.LongTrue ρ W v tb mat ls lt c low' u' := by
  intro b a ha
  rw [h b a ha]
  refine sum_congr rfl fun r _ => ?_
  rw [Road.Rows.eqN_same ls 0 (a := low) (a' := low')
    (fun j hj => by rw [Nat.zero_add]; exact hl j hj) r, ext_pt _ hu]

theorem lastOf_pt {z Z : Array E} {k : ℕ} (h : lastOf z k = .ok Z) {j : ℕ} (hj : j < k) :
    k ≤ z.size ∧ Road.pt ρ Z j = Road.pt ρ z (z.size - k + j) := by
  unfold lastOf cutLast at h
  by_cases hk : k > z.size
  · simp [hk, bind, Except.bind] at h
  · simp only [hk, if_false, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨by omega, Road.Rows.ptCut ρ z (Nat.le_refl _) (by omega)⟩

/-- **The three kinds of forms are worth the cells' extensions, where every table holds.** -/
theorem readsTrue_of_holds {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hy : layout h pc = .ok v.y) (S : Road.Switches h) (hs : scalesHeld h v.sc = .ok ())
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (Road.matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : tl.mats.map (fun M => (M.m, M.k)) = Road.matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd hd2 = some pts) (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF)
    (hfun : funsOf v.y H.fo pts r.2.1 = some funs) (M : Road.Mats K)
    (Hd : ∀ Fn ∈ funs, Road.Holds ρ W tl v.iU3 v.K3 M Fn) (hρ : Road.Numerals ρ) {D : Dim}
    (Z : Road.Sized h D) {P : Pub} (hyP : P.y = v.y)
    (hsz : H.wpl.r.size = P.rd.lNI + v.y.lPd - v.y.ls + v.y.h.la)
    (hla : v.y.h.la = v.y.ls + v.y.h.lt)
    (hNI : v.y.NI = D.nNu) (hPd : v.y.Pd = 2 ^ v.y.lPd) (hls : v.y.ls ≤ v.y.lPd)
    (hN : v.y.NI ≤ 2 ^ P.rd.lNI) (hB : v.y.h.d / v.y.S2 ≤ 2 ^ (v.y.lPd - v.y.ls))
    (hnl : v.y.xb.nl = 5) {l2 l46 : List Aff} (h2 : normsForms P v H = some l2)
    (h46 : rowsForms v H = some l46) {R : D6.Bridge.Run} (hXS : R.XS = XSof P v H)
    (hD : R.D = digitsOr v "P_V") (hD' : R.D' = digitsOr v "r_tV")
    (hgp : ∀ s, s < 5 → ρ.val (H.gp.getD s zeroE) = ρ.val R.gam ^ s) :
    letI : Scl := Road.sclOf h v.sc v.g v.y.Lam
    (∀ j, j < D.lT → Road.pt ρ H.PV j =
      Blocks.nat (R.P ρ (dataFF D (Road.cellsOf D (Road.cellsAt v.y M)) P.rd.lNI)) j) →
    (∀ j, j < P.rd.lNI + v.y.lPd + D.lT → Road.pt ρ H.wpl.r j = R.rS ρ j) →
    (∀ j, j < D.lT → Road.pt ρ H.tV.r j = R.rP ρ j) →
    R.ReadsTrue ρ (dataFF D (Road.cellsOf D (Road.cellsAt v.y M)) P.rd.lNI) v.y.lPd W := by
  letI : Scl := Road.sclOf h v.sc v.g v.y.Lam
  intro pP pS pR
  obtain ⟨Z1, _, T⟩ := Road.trueAt_of_holds ρ W hy S hg hrd hl ht htm hNM hp hzt hfun M Hd
  obtain ⟨ZV, hZV, T3⟩ := Road.trueAt3_of_holds ρ W hy S hg hrd hl ht htm hNM hp hfun M Hd
  have sh := (Road.admitted_of_layout hy S.p3).shape
  rw [sh] at T
  have F := Road.fits_of_layout_true hy S hs hg hrd hl ht hρ Z (Road.cellsAt v.y M) (Road.pt ρ Z1)
    (Road.pt ρ H.ztF) T
  rw [F.lT] at T3
  have eg : H.wpl.r.size - v.y.h.la = P.rd.lNI + v.y.lPd - v.y.ls := by omega
  have c1 : ∀ j, j < v.y.ls →
      Road.pt ρ ZV j = Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j) := by
    intro j hj
    rw [(lastOf_pt (ρ := ρ) hZV (j := j) (by omega)).2, eg]
  have c2 : ∀ j, j < D.lT → Road.pt ρ ZV (v.y.ls + j) =
      Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j) := by
    intro j hj
    have hlt := F.lT
    rw [(lastOf_pt (ρ := ρ) hZV (j := v.y.ls + j) (by omega)).2, eg, Nat.add_assoc]
  have T3' : Road.TrueAt3 ρ W v D.lT (Road.cellsAt v.y M)
      (fun j => Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j))
      (fun j => Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j))
      (Road.pt ρ H.PV) (Road.pt ρ H.tV.r) (Road.pt ρ H.ZE)
      (fun j => Road.pt ρ H.ZE (v.y.ls + j)) :=
    { xiV := fun b hb => longTrue_congr c1 c2 (T3.xiV b hb)
      afV := fun b hb => longTrue_congr c1 c2 (T3.afV b hb)
      arP := T3.arP
      arR := T3.arR
      xiE := T3.xiE }
  exact readsTrue_of_true F hyP T3' hNI hPd hls hN hB hnl h2 h46 hXS hD hD' hgp pP pS pR

#print axioms readsTrue_of_holds

end OnBytes.Desc.First.K4
