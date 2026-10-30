-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormsReads.lean: the norms' stage of the layers' own rounds: the forms' half:
at true reads, K4's three kinds of forms in the reads are worth the committed cells' extensions.

The per-position bridge of a norm (OnBytes/Desc/First/NormBridge/BridgeWorld.lean) asks a group of
premises `Run.ReadsTrue`: the 99 digits of each norm at the norms' token point, the streams' batch
at the squares' end point, and the 99 digits at the row products' end point, each as K4's form
through its read, are worth the extensions of the data's digits and limbs. Here that group follows,
at the data `dataFF` made of the library's cells (K4/NormsTarget.lean), from the library's two
records on a world: the layout fits (Fits) and the entries of five families of tables are true
(TrueAt3).

  `digitsOr_value`: one digit.
  `XSof_value`: the streams' batch: ONE extension at the layer's whole point.
  `readsTrue_of_true`: the law.

Limits. "The form at true reads equals it": algebra in a world. THAT THE READS ARE TRUE IS A PREMISE
(the row reads_are_true is another kind's). Fits and TrueAt3 are premises; nothing here shows that
they can hold at the layout of a shipped example. That the run's three points are the verifier's is
asked in three premises on coordinates. No draw, no soundness.
-/
import Johnson.Road.K4.NormsFormsZero
import OnBytes.Desc.First.K4.NormsTarget
import Johnson.Road.K4.SquaresSays
import Johnson.Road.Rows.GatedStartsProofs

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
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)

/-- The family of the rows' cells at a named point is found where the digits are there. -/
theorem digitsAt_found {v : Env} {Pn : String} {i : Nat} {Dg : Nat → Aff}
    (h : digitsAt v Pn i = some Dg) :
    ∃ b, v.tabAt ("ar@" ++ Pn) = some b := by
  unfold digitsAt at h
  obtain ⟨cells, hc, _⟩ := Option.map_eq_some_iff.mp h
  unfold Env.rowCells at hc
  obtain ⟨b, hb, _⟩ := Option.bind_eq_some_iff.mp hc
  exact ⟨b, hb⟩

/-- An extension reads the first g coordinates of its point alone. -/
theorem ext_pt {K : Type} [Field K] {g : ℕ} (f : ℕ → K) {z z' : ℕ → K}
    (h : ∀ j, j < g → z j = z' j) :
    ext g f z = ext g f z' := by
  unfold Blocks.ext
  refine sum_congr rfl fun X _ => ?_
  rw [Road.Rows.eqN_same g 0 (a := z) (a' := z') (fun j hj => by rw [Nat.zero_add]; exact h j hj) X]

/-- The library's list of group 2, whole. -/
theorem normsL_shape {v : Env} {P : Pub} {H : Heard} {l : List Aff}
    (h : Road.normsL P v H = some l) :
    ∃ txs tI tA e sum, P.y.T_ "xs" = some txs ∧ v.tabAt "xbI@Z_V" = some tI ∧
      v.tabAt "af@Z_V" = some tA ∧
      (hiTab H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e ∧
      Road.normsSum P.y v tI tA txs e H.gp = some sum ∧
      l = [H.wpl.row, Aff.slot H.wpl.sL - Aff.slot H.wpl.sR, Aff.slot H.wpl.sL + sum] := by
  obtain ⟨x0, l1, e0, h1, rfl⟩ := Road.appL_some h
  obtain ⟨x1, l2, e1, h2, rfl⟩ := Road.appL_some h1
  cases e0
  cases e1
  obtain ⟨txs, a1, h2⟩ := Road.bind_some h2
  obtain ⟨tI, a2, h2⟩ := Road.bind_some h2
  obtain ⟨tA, a3, h2⟩ := Road.bind_some h2
  obtain ⟨e, a4, h2⟩ := Road.bind_some h2
  obtain ⟨sum, a5, h2⟩ := Road.bind_some h2
  cases h2
  exact ⟨txs, tI, tA, e, sum, a1, a2, a3, a4, a5, rfl⟩

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {cc : Road.Cells K}
  {t : Cell → K} [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- One digit at the norms' token point, and at the row products' end point. -/
theorem digitsOr_value (F : Road.Fits ρ W v D cc t low u)
    (T3 : Road.TrueAt3 ρ W v D.lT cc lowV uV uP uR lowE uE) {i : Nat} :
    (∀ Dg, digitsAt v "P_V" i = some Dg → ∀ n, n < 99 →
        (digitsOr v "P_V" i n).value ρ W = ext D.lT (fun p => led t i p n) uP) ∧
      (∀ Dg, digitsAt v "r_tV" i = some Dg → ∀ n, n < 99 →
        (digitsOr v "r_tV" i n).value ρ W = ext D.lT (fun p => led t i p n) uR) := by
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  constructor
  · intro Dg h n hn
    obtain ⟨b, hb⟩ := digitsAt_found h
    unfold digitsOr
    rw [h]
    exact Road.K4.digitsAt_value F.num hb hrow hJ T (by rw [hm]; exact T3.arP b hb) h n hn
  · intro Dg h n hn
    obtain ⟨b, hb⟩ := digitsAt_found h
    unfold digitsOr
    rw [h]
    exact Road.K4.digitsAt_value F.num hb hrow hJ T (by rw [hm]; exact T3.arR b hb) h n hn

/-- The streams' batch through its read: one extension at the layer's whole point. -/
theorem XSof_value (F : Road.Fits ρ W v D cc t low u) {P : Pub} (hy : P.y = v.y) {H : Heard}
    (T3 : Road.TrueAt3 ρ W v D.lT cc (fun j => Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j))
      (fun j => Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j)) uP uR lowE uE)
    (hNI : v.y.NI = D.nNu) (hPd : v.y.Pd = 2 ^ v.y.lPd) (hls : v.y.ls ≤ v.y.lPd)
    (hN : v.y.NI ≤ 2 ^ P.rd.lNI) (hB : v.y.h.d / v.y.S2 ≤ 2 ^ (v.y.lPd - v.y.ls))
    {l : List Aff} (h : normsForms P v H = some l) :
    (XSof P v H).value ρ W =
      ext (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + D.lT)
        (Road.K4.sqV v.y.NI (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) v.y.lPd v.y.xb.nl D.lT
          (fun l => ρ.val (H.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
        (Road.pt ρ H.wpl.r) := by
  obtain ⟨txs, tI, tA, e, sum, a1, a2, a3, a4, a5, el⟩ :=
    normsL_shape (Road.K4.normsForms_normsL h)
  rw [hy] at a1 a4 a5
  have eX : XSof P v H = Aff.slot H.wpl.sL - (Aff.slot H.wpl.sL + sum) := by
    unfold XSof
    rw [h, el]
  have e3 := F.normsEnd T3 a2 a3 a1 hNI e H.gp H.wpl.sL a5
  have he' : hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls) = .ok e := by
    cases hh : hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls) with
    | ok a =>
      rw [hh] at a4
      have : a = e := by simpa [Except.toOption] using a4
      rw [this]
    | error s =>
      rw [hh] at a4
      simp [Except.toOption] at a4
  rw [eX, Aff.value_sub, e3, Aff.value_slot, sub_sub_cancel,
    ← Road.K4.squares_point ρ hls he' hN hB]
  simp only [hPd, F.S2]

/-- K4's vector of the squares is the bridge's table, at the data made of the cells. -/
theorem sqV_sqTab (lNI lPd : ℕ) (gp : ℕ → K) (gam : K) (hgp : ∀ l, l < 5 → gp l = gam ^ l) :
    Road.K4.sqV D.nNu D.d lPd 5 D.lT gp (fun ν l j p => bS D t ν l j p) =
      (dataFF D t lNI).sqTab lPd gam := by
  funext X
  unfold Road.K4.sqV D6.Bridge.Data.sqTab D6.Bridge.Data.batch
  show (if X / 2 ^ D.lT / 2 ^ lPd < D.nNu ∧ X / 2 ^ D.lT % 2 ^ lPd < D.d then _ else _) =
    (if X / 2 ^ D.lT / 2 ^ lPd < D.nNu ∧ X / 2 ^ D.lT % 2 ^ lPd < D.d then _ else _)
  split
  · exact sum_congr rfl fun l hl => by rw [hgp l (mem_range.mp hl)]; rfl
  · rfl

/-- **At true reads the three kinds of forms are worth the cells' extensions.** -/
theorem readsTrue_of_true (F : Road.Fits ρ W v D cc t low u) {P : Pub} (hy : P.y = v.y) {H : Heard}
    (T3 : Road.TrueAt3 ρ W v D.lT cc (fun j => Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j))
      (fun j => Road.pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j)) uP uR lowE uE)
    (hNI : v.y.NI = D.nNu) (hPd : v.y.Pd = 2 ^ v.y.lPd) (hls : v.y.ls ≤ v.y.lPd)
    (hN : v.y.NI ≤ 2 ^ P.rd.lNI) (hB : v.y.h.d / v.y.S2 ≤ 2 ^ (v.y.lPd - v.y.ls))
    (hnl : v.y.xb.nl = 5) {l2 l46 : List Aff} (h2 : normsForms P v H = some l2)
    (h46 : rowsForms v H = some l46) {R : D6.Bridge.Run} (hXS : R.XS = XSof P v H)
    (hD : R.D = digitsOr v "P_V") (hD' : R.D' = digitsOr v "r_tV")
    (hgp : ∀ s, s < 5 → ρ.val (H.gp.getD s zeroE) = ρ.val R.gam ^ s)
    (pP : ∀ j, j < D.lT → uP j = Blocks.nat (R.P ρ (dataFF D t P.rd.lNI)) j)
    (pS : ∀ j, j < P.rd.lNI + v.y.lPd + D.lT → Road.pt ρ H.wpl.r j = R.rS ρ j)
    (pR : ∀ j, j < D.lT → uR j = R.rP ρ j) :
    R.ReadsTrue ρ (dataFF D t P.rd.lNI) v.y.lPd W := by
  have hd : v.y.h.d / v.y.S2 * 2 ^ v.y.ls = D.d := by
    obtain ⟨n, hn⟩ := F.bd
    rw [F.d, F.S2, hn, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  refine { atP := ?_, atS := ?_, atR := ?_ }
  · intro i hi n hn
    obtain ⟨_, Dp, _, hp, _⟩ := rowsForms_mem h46 (i := i) (by rw [hNI]; exact hi)
    rw [hD, (digitsOr_value F T3).1 Dp hp n hn]
    exact ext_pt _ pP
  · rw [hXS, XSof_value F hy T3 hNI hPd hls hN hB h2, hd, hnl, hNI,
      sqV_sqTab P.rd.lNI v.y.lPd _ (ρ.val R.gam) hgp,
      show P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + D.lT = P.rd.lNI + v.y.lPd + D.lT by omega]
    exact ext_pt _ pS
  · intro i hi n hn
    obtain ⟨Dr, _, hr, _⟩ := rowsForms_mem h46 (i := i) (by rw [hNI]; exact hi)
    rw [hD', (digitsOr_value F T3).2 Dr hr n hn]
    exact ext_pt _ pR

#print axioms digitsOr_value
#print axioms XSof_value
#print axioms readsTrue_of_true

end OnBytes.Desc.First.K4
