-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PanelSidesEarly.lean: seven kinds of panel of the verifier's batched sumcheck have,
side by side, the form parts of the library's panels G, U, V, O, LR, D and QK.

Johnson/Road/FormsKeysEarly.lean shows for these seven kinds that the verifier's SHARE is the
library's. On its way each proof shows what the rows' weights and the forms of the A side are worth.
Here the same steps are taken to the statement SidesAre (Johnson/Road/K4/PanelSides.lean): the bits,
the A side with all its factors, and the B side, with the never-sent vectors and the vectors of the
weight claims set to 0.

Main names:
  `plain_w`: the bits of a place of a panel that plain appends.
  `sides_G`, `sides_U`, `sides_V`, `sides_O`, `sides_LR`, `sides_QK`: the A side is given as forms,
    the B side is a weight matrix.
  `sides_D`: the A side is a never-sent vector: both form parts are 0; only the bits are said.
  `panel_sides_early`: the seven under the record SigFits (Johnson/Road/FormsKeysPortSig.lean), for
    a panel b that IsPanelOf one of the seven; after the pattern of panel_term there.
Limits. The premises are those of shareP_G … shareP_QK without the one on the weight
claims' vectors, and two on the claim's and the call's weight; under SigFits these are paid as in
panel_term. The record of reads is rPort: it holds what the second token sumcheck SENT, and free
never-sent vectors (the head of Johnson/Road/FormsKeysPort.lean). Identities in one world: nothing
on a run, on soundness or on hiding.


-/
import Johnson.Road.K4.PanelSides
import Johnson.Road.FormsKeysPortSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff eqTab WsClaim WsShape)
open OnBytes.Model.Layer (Env Lay SBlk Panels PanelEnv ClaimEnv panelA panelT plain)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr LW Pan Rd call valU zpos wc)

/-- The panel that plain appends has the bits of its rows' numbers and of its columns'. -/
theorem plain_w {y : Lay} {ec : E} {claim : ℕ} {moeSet : Bool} {ny : ℕ}
    {A B : Option (ℕ → ℕ → Option Aff)} {wt : ℕ → E} {virt : Option ℕ} {s : Panels} {b : SBlk}
    (h : (plain y ec claim moeSet ny A B wt virt s).bl = s.bl.push b) :
    b.w = ceilLog2 b.ni + b.wy := by
  unfold plain at h
  have e := push_last h
  rw [← e]

section Sides

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low z zh : ℕ → K} (P : PortFits ρ W v D c t low z zh)
  (p : PanelEnv) (hp : p.v = v) (ec : E) (s : Panels) (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ)
  (w : ℕ → LW K) (q : ℕ) {om : Array E} {x : K}
include P hp

/-- The panel that the verifier appends for the segment G. -/
theorem sides_G (hel : ElTie ρ v D z q (call .G)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "G" s).bl = s.bl.push b) (hr : Returns b)
    (hom : omK ρ om b = Pan.G.om x) (hec : ρ.val ec = wc D z (call Pan.G.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .G := by
  obtain ⟨b', e', -, h2, -, h4', h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelG_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_G_eq]; exact hb)
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w (by rw [← panelA_G_eq]; exact hb)
  refine sides_weight_forms rfl rfl h2 h8 h7 hAf hr h5 h6 hwy hw hom (by rw [h4']; exact hec)
    (fun i hi => ?_) (hA _ fun _ _ => rfl)
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The panel that the verifier appends for the segment U. -/
theorem sides_U (hel : ElTie ρ v D z q (call .U)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "U" s).bl = s.bl.push b) (hr : Returns b)
    (hom : omK ρ om b = Pan.U.om x) (hec : ρ.val ec = wc D z (call Pan.U.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .U := by
  obtain ⟨b', e', -, h2, -, h4', h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelU_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_U_eq]; exact hb)
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w (by rw [← panelA_U_eq]; exact hb)
  refine sides_weight_forms rfl rfl h2 h8 h7 hAf hr h5 h6 hwy hw hom (by rw [h4']; exact hec)
    (fun i hi => ?_) (hA _ fun _ _ => rfl)
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The panel that the verifier appends for the segment V. -/
theorem sides_V (hel : ElTie ρ v D z q (call .V)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "V" s).bl = s.bl.push b) (hr : Returns b)
    (hom : omK ρ om b = Pan.V.om x) (hec : ρ.val ec = wc D z (call Pan.V.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .V := by
  obtain ⟨b', e', -, h2, -, h4', h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelV_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_V_eq]; exact hb)
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w (by rw [← panelA_V_eq]; exact hb)
  refine sides_weight_forms rfl rfl h2 h8 h7 hAf hr h5 h6 hwy hw hom (by rw [h4']; exact hec)
    (fun i hi => ?_) (hA _ fun _ _ => rfl)
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The panel that the verifier appends for the segment O. -/
theorem sides_O (hel : ElTie ρ v D z q (call .O)) (h4 : v.y.h.p4 = true)
    (ho : HasShort ρ W v D c t (zpos D z) .o) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "O" s).bl = s.bl.push b) (hr : Returns b)
    (hom : omK ρ om b = Pan.O.om x) (hec : ρ.val ec = wc D z (call Pan.O.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .O := by
  obtain ⟨b', e', -, h2, -, h4', h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelO_spec P.fits h4 ho p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_O_eq]; exact hb)
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w (by rw [← panelA_O_eq]; exact hb)
  refine sides_weight_forms rfl rfl h2 h8 h7 hAf hr h5 h6 hwy hw hom (by rw [h4']; exact hec)
    (fun i hi => ?_) (hA _ fun _ _ => rfl)
  have hi' : i < D.nl := hi
  unfold wtK
  rw [hwt i (by rw [P.fits.Lam]; exact hi'), hel i hi']
  rfl

/-- The panel that the verifier appends for the segment LR. -/
theorem sides_LR (hel : ElTie ρ v D z q (call .LR)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "LR" s).bl = s.bl.push b) (hr : Returns b)
    (hom : omK ρ om b = Pan.LR.om x) (hec : ρ.val ec = wc D z (call Pan.LR.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .LR := by
  obtain ⟨b', e', -, h2, -, h4', h5, h6, h7, h8, -, ⟨Af, hAf, hA⟩, hwt⟩ :=
    panelLR_spec P.fits p hp ec (eqTab (v.zl q)) s
  obtain rfl : b = b' := push_last (hb.symm.trans e')
  have hwy : b.wy = ceilLog2 b.ny := plain_wy (by rw [← panelA_LR_eq]; exact hb)
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w (by rw [← panelA_LR_eq]; exact hb)
  refine sides_weight_forms rfl rfl h2 h8 h7 hAf hr h5 h6 hwy hw hom (by rw [h4']; exact hec)
    (fun i hi => ?_) (hA _ fun _ _ => rfl)
  have hi' : i < D.ne := hi
  have hl : 2 * i + 1 < D.nl := by
    unfold Inst.Model.FFSeg.Dim.ne at hi'
    omega
  unfold wtK
  rw [hwt i (by rw [P.fits.LamM]; exact hi'), hel (2 * i + 1) hl]
  rfl

/-- The panel that the verifier appends for the segment D: its A side is the never-sent vector
number 0, its B side a weight matrix. -/
theorem sides_D (_hel : ElTie ρ v D z q (call .D)) {b : SBlk}
    (hb : (panelA p ec (eqTab (v.zl q)) "D" s).bl = s.bl.push b)
    (_hom : omK ρ om b = Pan.D.om x) (_hec : ρ.val ec = wc D z (call Pan.D.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .D := by
  subst hp
  rw [panelA_D_eq] at hb
  have hwy : b.wy = ceilLog2 b.ny := plain_wy hb
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w hb
  unfold plain at hb
  have e := push_last hb
  subst e
  exact sides_virt rfl rfl (k := 0) (v0 := s.nextV) rfl rfl P.fits.Lam P.fits.f hwy hw

/-- The panel that the verifier appends for the segment QK: its A side reads the array a at the end
point of the second token sumcheck. -/
theorem sides_QK (hel : ElTie ρ v D z q (call .QK)) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "QK" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b) (hom : omK ρ om b = Pan.QK.om x)
    (hec : ρ.val ec = wc D z (call Pan.QK.fam)) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh x b .QK := by
  subst hp
  rw [panelT_QK_plain] at hs
  have e0 := (Option.some.inj hs).symm
  subst e0
  have hwy : b.wy = ceilLog2 b.ny := plain_wy hb
  have hw : b.w = ceilLog2 b.ni + b.wy := plain_w hb
  unfold plain at hb
  have e := push_last hb
  subst e
  refine sides_weight_forms rfl rfl rfl rfl rfl rfl hr P.fits.Lam P.fits.d hwy hw hom hec
    (fun i hi => ?_) (fun i k2 a ha => ?_)
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

end Sides

section Whole

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv}
  {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
  {lk L0 : ℕ} {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- **The seven early kinds and QK's, under SigFits.** hr: the forms of the sides of b are there, if
b is a panel whose sides are read as forms. hh: the never-sent vectors in the record rPort, free;
w: the weights in the library's B sides, free (no B side of these seven is a form part). -/
theorem panel_sides_early (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb)
    (hh : ℕ → ℕ → K) (w : ℕ → LW K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {cl : List WsClaim}
    {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1) {b : SBlk} {pn : Pan}
    (hI : IsPanelOf p c TS cl b pn)
    (hpn : pn = .G ∨ pn = .U ∨ pn = .O ∨ pn = .D ∨ pn = .V ∨ pn = .LR ∨ pn = .QK)
    (hr : b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) → Returns b) :
    SidesAre ρ Wo p.v.y om D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b pn := by
  have hAC := callsAC_of_lines S.lines
  cases pn with
  | G =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.G).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    exact sides_G S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide))
      hbl (hr ht (f3 rfl) fun _ _ => f2) (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | U =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.U).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    exact sides_U S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide))
      hbl (hr ht (f3 rfl) fun _ _ => f2) (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | O =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.O).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    exact sides_O S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide)) S.p4 S.o
      hbl (hr ht (f3 rfl) fun _ _ => f2) (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | D =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.D).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    exact sides_D S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide))
      hbl (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | V =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.V).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    exact sides_V S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide))
      hbl (hr ht (f3 rfl) fun _ _ => f2) (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | LR =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.LR).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    exact sides_LR S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide))
      hbl (hr ht (f3 rfl) fun _ _ => f2) (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | QK =>
    obtain ⟨v0, -, ht, q, hq, g, hg, H⟩ := hI
    obtain ⟨st, st', l, hn, hst, hs, hbl, -, -, -⟩ := id H
    rw [hTS] at hq
    have hq' : q = (call Fam.QK).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2, f3⟩ := facts_QK hs hbl
    exact sides_QK S.port p rfl _ st hh tb L0 w q (by rw [hq']; exact S.el _ (by decide)) hs hbl
      (hr ht f3 fun _ _ => f2) (omK_om f1 hom) (by rw [hq']; exact S.wc _ (by decide))
  | _ => simp at hpn

end Whole

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.panel_sides_early
