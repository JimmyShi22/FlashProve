-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysEarly.lean: the shares of seven of the verifier's panels in the sum of the
batched sumcheck are the library's shares of its panels G, U, V, O, LR, D and QK.

The batched sumcheck of a layer sub-proof runs on the inner product of two long vectors, which are
made of panels (OnBytes/Model/LayerPanels.lean). Johnson/Road/FormsKeysEnd.lean writes that inner
product as a sum of shares, one for each panel. The library writes its own sum of shares (Pan.share
in Inst/Model/FF/Objects.lean). This file compares the two, panel by panel, for the seven kinds of
panel with two factors whose B side is a weight matrix.

What is compared with what: what the verifier's own panelA and panelT append for a segment, through
shareP, a definition of Johnson/Road/FormsKeysPort.lean on that panel, with the library's own
Pan.wt, Pan.A and Pan.B, through shareL, which is the library's Pan.share without the call's weight
(share_wc there). The record of reads is rPort of that file.

Main theorems.
 - share_of_rows, share_weight_forms: the share of a panel with two factors from its rows, columns,
   rows' weights and the products of its two sides.
 - shareP_G, shareP_U, shareP_V, shareP_O, shareP_LR, shareP_D (panels of the lookup's join) and
   shareP_QK (a panel of the second token sumcheck's terms): shareP of the panel is the reading of
   the call's weight ec times shareL of the library's panel.

Which value is which. The A sides of G, U, V, O, LR and QK are forms in entries of the reads, which
are hidden values. The A side of D is the never-sent vector number 0; it is free here, and rPort has
it for the library's Hh1. The B sides are the vectors wv of the weight claims; they are free here
and tied to the library's Pan.B by the hypothesis WvRows. The call's weight and the rows' weights
are public. None of the seven reads a value that was sent.

The panel D. The verifier's A side holds the never-sent vector at all f columns of a row. In the row
of a layer with routed experts the library's A side is 0 from column fe on, and so is its B side; in
the row of another layer neither is cut (fSh in Inst/Model/FF/Objects.lean). So on a layer with
routed experts the two A sides differ, and the products of the two sides agree column by column.

The hypotheses, and where they are met. No witness of them is given here as a term. PortFits:
portFits_of_layout (Johnson/Road/FormsKeysPortFits.lean) concludes it. ElTie, that the layers'
weights in the point of the verifier's call number q are the library's for the call of the panel's
family: asked of that one call; q is any number; elTie_of_tie in the same file concludes it.
Returns, that the forms of a panel's A side are there: returns_of_stackEnd
(Johnson/Road/FormsKeysRet.lean). WvRows, that the vectors of the panel's weight claims are the rows
of Pan.B and 0 past its columns: Johnson/Road/FormsKeysWvB.lean. For O: the profile is 4, and the
array o is found, tied and true, as in panelO_spec (Johnson/Road/FormsKeysW.lean). The run of
Johnson/Road/FormsKeysRunP.lean evaluates the conclusion: it compares each
share with the library's
Pan.share, at made-up numbers, in a world that is made true by the way it is written. It tests
neither Returns nor WvRows.

What is not claimed. The call's weight ec is not compared with the library's wc. That q is the
number of the call that holds the segment is not asked and not shown. That the verifier's list of
panels is the library's list is not shown here. Nothing is said of the eight other kinds of panel,
of the place of a panel in the long vectors, or of what makes the sum of the shares what the
sumcheck claims. All statements are identities in a world. The program does not import this file.
-/
import Johnson.Road.FormsKeysPort
import Johnson.Road.FormsKeysW

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab)
open OnBytes.Model.Layer (Env Lay SBlk Panels PanelEnv panelA panelT plain)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr LW Pan Rd call valU zpos fSh)

/-! ## Tools -/

/-- What is pushed onto an array can be read off the result. -/
theorem push_last {α : Type} {a : Array α} {x y : α} (h : a.push x = a.push y) : x = y := by
  have h1 := congrArg Array.back? h
  simpa using h1

/-- The panel that plain appends has as many bits of a column's number as its columns need. -/
theorem plain_wy {y : Lay} {ec : E} {claim : ℕ} {moeSet : Bool} {ny : ℕ}
    {A B : Option (ℕ → ℕ → Option Aff)} {wt : ℕ → E} {virt : Option ℕ} {s : Panels} {b : SBlk}
    (h : (plain y ec claim moeSet ny A B wt virt s).bl = s.bl.push b) :
    b.wy = ceilLog2 b.ny := by
  unfold plain at h
  have e := push_last h
  rw [← e]

section General

variable {K : Type} [Field K] (ρ : Reading K) (W : World K) (y : Lay) (hv wv : ℕ → ℕ → K)

/-- The share of a panel with two factors, from its rows and columns. If the panel has nr rows with
the weights wt, the product of what is left of its two sides is A B on the first nc columns, and 0
on the columns from nc on, then its share is the call's weight times the sum over the rows of the
row's weight times the inner product of the rows of A and B. -/
theorem share_of_rows {b : SBlk} (ht : b.tri = false) {nr nc : ℕ} (wt : ℕ → K)
    (A B : ℕ → ℕ → K) (hni : b.ni = nr) (hnc : nc ≤ 2 ^ b.wy)
    (hwt : ∀ i, i < nr → wtK ρ b i = wt i)
    (hin : ∀ i, i < nr → ∀ yv, yv < nc →
      aRaw ρ W hv b i yv * bRaw ρ W wv b i yv = A i yv * B i yv)
    (hout : ∀ i, i < nr → ∀ yv, nc ≤ yv → yv < 2 ^ b.wy →
      aRaw ρ W hv b i yv * bRaw ρ W wv b i yv = 0) :
    shareP ρ W y hv wv b =
      ρ.val b.ec * ∑ i ∈ range nr, wt i * ∑ ι ∈ range nc, A i ι * B i ι := by
  unfold shareP nRows rowW
  simp only [ht, Bool.false_eq_true, ↓reduceIte]
  rw [hni]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < nr := mem_range.mp hi
  rw [hwt i hi', ← Finset.sum_subset (range_subset_range.mpr hnc)]
  · congr 1
    exact sum_congr rfl fun yv hy => hin i hi' yv (mem_range.mp hy)
  · intro yv h1 h2
    exact hout i hi' yv (Nat.le_of_not_lt fun h => h2 (mem_range.mpr h)) (mem_range.mp h1)

/-- The same for a panel whose A side is given as forms and whose B side is a weight matrix: the
forms are there and are worth A; the vectors of the panel's weight claims are the rows of B. -/
theorem share_weight_forms {b : SBlk} (ht : b.tri = false) (hk : b.virt = none) {v0 : ℕ}
    (h0 : b.v0 = some v0) {Af : ℕ → ℕ → Option Aff} (hAf : b.A = some Af) (hr : Returns b)
    {nr nc : ℕ} (wt : ℕ → K) (A B : ℕ → ℕ → K) (hni : b.ni = nr) (hny : b.ny = nc)
    (hnc : nc ≤ 2 ^ b.wy) (hwt : ∀ i, i < nr → wtK ρ b i = wt i)
    (hA : ∀ i k2 a, Af i k2 = some a → a.value ρ W = A i k2)
    (hw : WvRows wv v0 b.ni b.wy nc B) :
    shareP ρ W y hv wv b =
      ρ.val b.ec * ∑ i ∈ range nr, wt i * ∑ ι ∈ range nc, A i ι * B i ι := by
  have hB : ∀ i yv, bRaw ρ W wv b i yv = wv (v0 + i) yv := by
    intro i yv
    unfold bRaw
    rw [ht, hk, h0]
  refine share_of_rows ρ W y hv wv ht wt A B hni hnc hwt ?_ ?_
  · intro i hi yv hy
    have hi' : i < b.ni := by rw [hni]; exact hi
    have hy' : yv < b.ny := by rw [hny]; exact hy
    obtain ⟨a, ha⟩ := hr.1 Af hAf i hi' yv hy'
    have e1 : aRaw ρ W hv b i yv = A i yv := by
      unfold aRaw
      rw [ht, hk]
      show (if yv < b.ny then sideK ρ W b.A i yv else 0) = _
      rw [if_pos hy', hAf]
      show ov ρ W (Af i yv) = _
      rw [ha]
      exact hA i yv a ha
    rw [e1, hB, hw i hi' yv (lt_of_lt_of_le hy hnc), if_pos hy]
  · intro i hi yv h1 h2
    have hi' : i < b.ni := by rw [hni]; exact hi
    rw [hB, hw i hi' yv h2, if_neg (Nat.not_lt.mpr h1), mul_zero]

end General

/-! ## What the verifier appends for the segments D and QK -/

/-- What panelA appends for the segment D. -/
theorem panelA_D_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelA p ec el "D" s = plain p.v.y ec 0 false p.v.y.h.f none none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkd))
      (some 0) s := rfl

/-- What panelT appends for the segment QK. -/
theorem panelT_QK_plain (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "QK" s = some (plain p.v.y ec 1 false p.v.y.h.d
      (some fun lam k2 => p.v.shIn (p.v.tensorAt "a" "rt") lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkq))
      none s) := rfl

/-! ## The seven shares -/

section Shares

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low z zh : ℕ → K} (P : PortFits ρ W v D c t low z zh)
  (p : PanelEnv) (hp : p.v = v) (ec : E) (s : Panels) (hv wv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ)
  (w : ℕ → LW K) (q : ℕ)
include P hp

/-- The share of the panel that the verifier appends for the segment G is the call's weight times
the library's share of Pan.G without its call's weight, at the record rPort. -/
theorem shareP_G (hel : ElTie ρ v D z q (call .G)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "G" s).bl = s.bl.push b) (hr : Returns b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.G.nc D)
      (Pan.G.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .G := by
  obtain ⟨b', e', -, h2, -, h4, h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelG_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_G_eq]; exact hb)
  rw [← h4]
  refine share_weight_forms ρ W v.y hv wv h2 h8 h7 hAf hr _ _ _ h5 h6
    (by rw [← h6, hwy]; exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_)
    (hA _ fun _ _ => rfl) hw
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The share of the panel that the verifier appends for the segment U is the call's weight times
the library's share of Pan.U without its call's weight, at the record rPort. -/
theorem shareP_U (hel : ElTie ρ v D z q (call .U)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "U" s).bl = s.bl.push b) (hr : Returns b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.U.nc D)
      (Pan.U.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .U := by
  obtain ⟨b', e', -, h2, -, h4, h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelU_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_U_eq]; exact hb)
  rw [← h4]
  refine share_weight_forms ρ W v.y hv wv h2 h8 h7 hAf hr _ _ _ h5 h6
    (by rw [← h6, hwy]; exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_)
    (hA _ fun _ _ => rfl) hw
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The share of the panel that the verifier appends for the segment V is the call's weight times
the library's share of Pan.V without its call's weight, at the record rPort. -/
theorem shareP_V (hel : ElTie ρ v D z q (call .V)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "V" s).bl = s.bl.push b) (hr : Returns b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.V.nc D)
      (Pan.V.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .V := by
  obtain ⟨b', e', -, h2, -, h4, h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelV_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_V_eq]; exact hb)
  rw [← h4]
  refine share_weight_forms ρ W v.y hv wv h2 h8 h7 hAf hr _ _ _ h5 h6
    (by rw [← h6, hwy]; exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_)
    (hA _ fun _ _ => rfl) hw
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The same for the segment O, at profile 4. h4: the profile; ho: the array o is found, tied and
true at the library's token point. -/
theorem shareP_O (hel : ElTie ρ v D z q (call .O)) (h4 : v.y.h.p4 = true)
    (ho : HasShort ρ W v D c t (zpos D z) .o) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "O" s).bl = s.bl.push b) (hr : Returns b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.O.nc D)
      (Pan.O.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .O := by
  obtain ⟨b', e', -, h2, -, h4', h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelO_spec P.fits h4 ho p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_O_eq]; exact hb)
  rw [← h4']
  refine share_weight_forms ρ W v.y hv wv h2 h8 h7 hAf hr _ _ _ h5 h6
    (by rw [← h6, hwy]; exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_)
    (hA _ fun _ _ => rfl) hw
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The same for the segment LR: row i belongs to layer 2 i + 1 of the group. -/
theorem shareP_LR (hel : ElTie ρ v D z q (call .LR)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "LR" s).bl = s.bl.push b) (hr : Returns b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.LR.nc D)
      (Pan.LR.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .LR := by
  obtain ⟨b', e', -, h2, -, h4, h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelLR_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_LR_eq]; exact hb)
  rw [← h4]
  refine share_weight_forms ρ W v.y hv wv h2 h8 h7 hAf hr _ _ _ h5 h6
    (by rw [← h6, hwy]; exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_)
    (hA _ fun _ _ => rfl) hw
  have hi' : i < D.ne := hi
  have hl : 2 * i + 1 < D.nl := by
    unfold Inst.Model.FFSeg.Dim.ne at hi'
    omega
  unfold wtK
  rw [hwt i (by rw [P.fits.LamM]; exact hi'), hel (2 * i + 1) hl]
  rfl

/-- The same for the segment D. The verifier's A side is the never-sent vector number 0, at all f
columns of a row; the library's is 0 from column fSh on, which is fe on a layer with routed experts
and f on another. The library's B side is 0 from there on too, so the products of the two sides
agree column by column. -/
theorem shareP_D (hel : ElTie ρ v D z q (call .D)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "D" s).bl = s.bl.push b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.D.nc D)
      (Pan.D.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .D := by
  subst hp
  rw [panelA_D_eq] at hb
  have hwy : b.wy = ceilLog2 b.ny := plain_wy hb
  unfold plain at hb
  have e := push_last hb
  subst e
  refine share_of_rows ρ W p.v.y hv wv rfl (Pan.D.wt D z)
    (Pan.D.A D (rPort ρ p.v.y p.shownT hv D t z zh))
    (Pan.D.B D (rPort ρ p.v.y p.shownT hv D t z zh) tb L0 w z zh) P.fits.Lam
    (by
      show D.f ≤ 2 ^ ceilLog2 p.v.y.h.f
      rw [← P.fits.f]
      exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_) (fun i hi yv hy => ?_)
    (fun i hi yv h1 h2 => ?_)
  · have hi' : i < D.nl := hi
    have hL : i < p.v.y.Lam := by rw [P.fits.Lam]; exact hi'
    show ρ.val (((Array.range p.v.y.Lam).map fun i =>
      mulE ((eqTab (p.v.zl q)).getD i zeroE) (Model.Layer.pw
        (Model.Layer.tOf (p.v.sc.kl (p.v.lay i) Model.Layer.Lkd)))).getD i zeroE) = _
    rw [range_map_getD _ _ hL, P.fits.kd i hi', scl_weight P.fits.num, hel i hi']
    rfl
  · have hi' : i < p.v.y.Lam := by rw [P.fits.Lam]; exact hi
    have hy2 : yv < 2 ^ ceilLog2 p.v.y.h.f := by
      have h1 : yv < D.f := hy
      rw [← P.fits.f] at h1
      exact lt_of_lt_of_le h1 (Slice.le_two_pow_ceilLog2 _)
    have e2 := hw i hi' yv hy2
    rw [if_pos hy] at e2
    show hv 0 (i * 2 ^ ceilLog2 p.v.y.h.f + yv) * wv (s.nextV + i) yv = _
    rw [e2]
    by_cases hf : yv < fSh D i
    · show _ = (if yv < fSh D i then hv 0 (i * 2 ^ ceilLog2 p.v.y.h.f + yv) else 0) * _
      rw [if_pos hf]
    · have e3 : Pan.D.B D (rPort ρ p.v.y p.shownT hv D t z zh) tb L0 w z zh i yv = 0 := by
        show (if yv < fSh D i then _ else 0) = 0
        rw [if_neg hf]
      rw [e3, mul_zero, mul_zero]
  · have hi' : i < p.v.y.Lam := by rw [P.fits.Lam]; exact hi
    have e2 := hw i hi' yv h2
    rw [if_neg (Nat.not_lt.mpr h1)] at e2
    show hv 0 (i * 2 ^ ceilLog2 p.v.y.h.f + yv) * wv (s.nextV + i) yv = 0
    rw [e2, mul_zero]

/-- The same for the segment QK, a panel of the second token sumcheck's terms: its A side reads the
array a at the end point of that sumcheck. -/
theorem shareP_QK (hel : ElTie ρ v D z q (call .QK)) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "QK" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b)
    (hw : WvRows wv s.nextV b.ni b.wy (Pan.QK.nc D)
      (Pan.QK.B D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh)) :
    shareP ρ W v.y hv wv b =
      ρ.val ec * shareL D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh .QK := by
  subst hp
  rw [panelT_QK_plain] at hs
  have e0 := (Option.some.inj hs).symm
  subst e0
  have hwy : b.wy = ceilLog2 b.ny := plain_wy hb
  unfold plain at hb
  have e := push_last hb
  subst e
  refine share_weight_forms ρ W p.v.y hv wv rfl rfl rfl rfl hr (Pan.QK.wt D z)
    (Pan.QK.A D (rPort ρ p.v.y p.shownT hv D t z zh))
    (Pan.QK.B D (rPort ρ p.v.y p.shownT hv D t z zh) tb L0 w z zh) P.fits.Lam P.fits.d
    (by
      show D.d ≤ 2 ^ ceilLog2 p.v.y.h.d
      rw [← P.fits.d]
      exact Slice.le_two_pow_ceilLog2 _) (fun i hi => ?_) (fun i k2 a ha => ?_) hw
  · have hi' : i < D.nl := hi
    have hL : i < p.v.y.Lam := by rw [P.fits.Lam]; exact hi'
    show ρ.val (((Array.range p.v.y.Lam).map fun i =>
      mulE ((eqTab (p.v.zl q)).getD i zeroE) (Model.Layer.pw
        (Model.Layer.tOf (p.v.sc.kl (p.v.lay i) Model.Layer.Lkq)))).getD i zeroE) = _
    rw [range_map_getD _ _ hL, P.fits.kq i hi', scl_weight P.fits.num, hel i hi']
    rfl
  · have ha' : p.v.shA "a" "rt" i k2 = some a := ha
    obtain ⟨ten, tb', h1, T, R⟩ := P.short2 .a rfl
    show _ = valU D t .a i k2 zh
    rw [shA_true P.fits.num T R h1 ha', ext_raw D t zh rfl]

end Shares

#print axioms share_of_rows
#print axioms share_weight_forms
#print axioms shareP_G
#print axioms shareP_U
#print axioms shareP_V
#print axioms shareP_O
#print axioms shareP_LR
#print axioms shareP_D
#print axioms shareP_QK

end OnBytes.Road
