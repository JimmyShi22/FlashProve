-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PanelSidesLate.lean: the eight kinds of the verifier's panels that hold a value
which the prover has sent have, side by side, the form parts of the library's panels N1, N2, XR, DD,
MR, Gr l, Ur l and Dr l.

Johnson/Road/FormsKeysLate.lean compares the SHARES of these eight kinds: sums of products of the
two sides. Here each side is compared by itself, in the words of SidesAre
(Johnson/Road/K4/PanelSides.lean), where the never-sent vectors and the vectors of the weight claims
are set to 0. What a row's weight and a side's form are worth is shown as in the proofs of shareP_N1
to shareP_Dr there, with the same lemmas. In N1, N2, XR, DD and MR each of the two sides, and
in Gr l and Ur l the A side, is the library's by itself; of Dr l only the bits are compared.

Main names:
  `omK_late`: the weight of claim 1 is the library's weight of a late panel's claim.
  `ceil_max_one`: the rounded-up logarithm of max n 1 is that of n.
  `sides_blk_forms`: SidesAre for the panel blkPlain of claim 1 with both sides given as forms.
  `sides_blk_tri`: SidesAre for the panel blkTri of claim 1 whose column factor is given as forms.
  `sides_N1`, `sides_N2`, `sides_XR`, `sides_DD`, `sides_MR`: SidesAre for the panel that panelT has
    appended for that segment.
  `sides_Gr`, `sides_Ur`, `sides_Dr`: SidesAre for the panel that triStep has appended for the
    segment G, U or D and one layer with routed experts.
  `panel_sides_late`: the eight in one, under SigFits, for a panel with the mark of one of these
    eight kinds of the library's panels.
Limits. Identities in one world. The record is rPort: it holds the SENT end values of the second
token sumcheck where the library's true record has contractions of the cells, so nothing is said on
what these values are. For Gr l and Ur l the B side, and for Dr l both sides, are said to be 0 at
the vectors 0 and no more: what the weight claims' vectors and the never-sent vectors hold is not
compared here. That PortFits, the ties or SigFits can be met is not shown here (see the heads of
Johnson/Road/FormsKeysLate.lean and Johnson/Road/FormsKeysPortSig.lean). The panel QK and the six
early kinds are not here. Nothing on the panels' places, on a run or on soundness.


-/
import Johnson.Road.K4.PanelSides
import Johnson.Road.FormsKeysPortSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff eqTab WsShape WsClaim)
open OnBytes.Model.Layer (Env Lay SBlk Panels PanelEnv ClaimEnv panelT kT sumE)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr LW Pan Rd wc call valU xU)
open Cb.Pv.Lay.At (isVirt)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A panel of claim 1 has the library's weight of the claim of a late panel. -/
theorem omK_late {ρ : Reading K} {om : Array E} {b : SBlk} {pn : Pan} (hc : b.claim = 1)
    (hl : pn.late = true) : omK ρ om b = pn.om (ρ.val (om.getD 1 zeroE)) := by
  unfold omK Pan.om
  rw [hc, if_pos hl]

/-- The rounded-up logarithm of max n 1 is that of n. -/
theorem ceil_max_one (n : ℕ) : ceilLog2 (max n 1) = ceilLog2 n := by
  rw [ceilLog2_eq_clog, ceilLog2_eq_clog]
  rcases Nat.eq_zero_or_pos n with e | e
  · rw [e]
    simp
  · rw [Nat.max_eq_left e]

section Blocks
variable [scl : Scl] {ρ : Reading K} {W : World K} {y : Lay} {om : Array E} {D : Dim} {r : Rd K}
  {tb : Tables} {L0 : ℕ} {w : ℕ → LW K} {z zh : ℕ → K} {pn : Pan}

/-- The panel that plain appends for claim 1 with both sides given as forms, against a late panel pn
of the library whose A side is no never-sent vector and whose B side is no weight matrix. Asked: the
forms are there; the rows and columns are those of pn; the call's weight, the rows' weights and, on
the rows and columns of pn, the forms of the two sides are worth what pn has. -/
theorem sides_blk_forms (hv : isVirt pn = false) (hg : pn.weight = false) (hl : pn.late = true)
    {ec : E} {moeSet : Bool} {ny : ℕ} {A B : ℕ → ℕ → Option Aff} {wt : ℕ → E} {nv : ℕ}
    (hr : Returns (blkPlain y ec 1 moeSet ny (some A) (some B) wt none nv))
    (hni : (if moeSet then y.LamM else y.Lam) = pn.nr D) (hny : ny = pn.nc D)
    (hec : ρ.val ec = wc D z (call pn.fam))
    (hwt : ∀ i, i < pn.nr D → ρ.val (wt (if moeSet then 2 * i + 1 else i)) = pn.wt D z i)
    (hA : ∀ i yv a, i < pn.nr D → yv < pn.nc D →
      A (if moeSet then 2 * i + 1 else i) yv = some a → a.value ρ W = pn.A D r i yv)
    (hB : ∀ i yv a, i < pn.nr D → yv < pn.nc D →
      B (if moeSet then 2 * i + 1 else i) yv = some a →
        a.value ρ W = pn.B D r tb L0 w z zh i yv) :
    SidesAre ρ W y om D r tb L0 w z zh (ρ.val (om.getD 1 zeroE))
      (blkPlain y ec 1 moeSet ny (some A) (some B) wt none nv) pn :=
  sides_forms hv hg rfl rfl rfl rfl rfl hr hni hny rfl rfl (omK_late rfl hl) hec
    (fun i hi => by
      have hi' : i < (if moeSet then y.LamM else y.Lam) := by
        rw [hni]
        exact hi
      show ρ.val (((Array.range (if moeSet then y.LamM else y.Lam)).map fun i =>
        wt (if moeSet then 2 * i + 1 else i)).getD i zeroE) = _
      rw [range_map_getD _ _ hi']
      exact hwt i hi)
    hA hB

/-- The panel that tri appends for claim 1 with the column factor given as forms, against a late
panel pn of the library whose A side is no never-sent vector and whose B side is a weight matrix.
Asked: the experts are the rows of pn and nk its columns; the call's weight is that of pn; on the
rows and columns of pn the panel's weight times the selector's factor times the column's form is
worth the row's weight of pn times its A side. -/
theorem sides_blk_tri (hv : isVirt pn = false) (hg : pn.weight = true) (hl : pn.late = true)
    {ec : E} {nk : ℕ} {sl : Array E} {xx : Array Aff} {wt : E} {nv : ℕ}
    (hne : y.h.NE = pn.nr D) (hny : nk = pn.nc D) (hec : ρ.val ec = wc D z (call pn.fam))
    (hA : ∀ i yv, i < pn.nr D → yv < pn.nc D →
      ρ.val wt * ρ.val (sl.getD i zeroE) * (xx.getD yv {}).value ρ W =
        pn.wt D z i * pn.A D r i yv) :
    SidesAre ρ W y om D r tb L0 w z zh (ρ.val (om.getD 1 zeroE))
      (blkTri y ec 1 nk sl xx none wt nv) pn :=
  sides_tri_forms hv hg rfl rfl rfl hne hny rfl rfl (ceil_max_one _) (omK_late rfl hl) hec hA

end Blocks

section Kinds

variable [scl : Scl] {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {low z zh : ℕ → K} {om : Array E}

/-! ## The five kinds whose two sides are forms -/

/-- THE PANEL OF N1. If panelT returns for the segment N1, with the layers' weights in the point of
call number q and a call's weight ec that reads as the library's, and b is the panel that it has
appended, whose forms are there, then b has the bits and the two sides of the library's panel N1 at
the record rPort. Asked beside: PortFits and the three ties of shareP_N1. hp: the panels are made
from the environment of PortFits. -/
theorem sides_N1 (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.N1)) (hE : EwTie ρ v D z Fam.N1)
    (hT : WtsTie ρ v D low Fam.N1) (p : PanelEnv) (hp : p.v = v) {ec : E}
    (hec : ρ.val ec = wc D z (call Fam.N1)) (s : Panels) (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "N1" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b .N1 := by
  subst hp
  rw [panelT_N1_eq] at hs
  obtain ⟨wh, hwh, e⟩ := of_bind_some hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  obtain ⟨ew, hew⟩ := ewOf_of_ewh hwh
  have hW : Wts ρ ew wh p.v.y.ls low D.d := hT ew wh hew hwh
  refine sides_blk_forms (pn := .N1) rfl rfl rfl hr P.fits.Lam rfl hec (fun i hi => hel i hi)
    (fun i yv a _ _ ha => ?_) (fun i yv a hi _ ha => ?_)
  · obtain rfl := Option.some.inj ha
    exact Aff.value_ofConst ρ W _
  · have hi' : i < D.nl := hi
    have ha' : p.v.SxsA wh "Y" (2 * i) = some a := ha
    show a.value ρ W = ∑ x ∈ range D.d,
      Inst.Model.FFSeg.ew D z (if (2 * i) % 2 = 0 then Fam.N1 else Fam.N2) x * xU D t (2 * i) x zh
    rw [P.Sxs2 hW (by omega) ha', if_pos (by omega)]
    exact sum_congr rfl fun x hx => by rw [← (hE ew hew).2 x (mem_range.mp hx)]

/-- THE PANEL OF N2: as sides_N1. -/
theorem sides_N2 (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.N2)) (hE : EwTie ρ v D z Fam.N2)
    (hT : WtsTie ρ v D low Fam.N2) (p : PanelEnv) (hp : p.v = v) {ec : E}
    (hec : ρ.val ec = wc D z (call Fam.N2)) (s : Panels) (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "N2" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b .N2 := by
  subst hp
  rw [panelT_N2_eq] at hs
  obtain ⟨wh, hwh, e⟩ := of_bind_some hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  obtain ⟨ew, hew⟩ := ewOf_of_ewh hwh
  have hW : Wts ρ ew wh p.v.y.ls low D.d := hT ew wh hew hwh
  refine sides_blk_forms (pn := .N2) rfl rfl rfl hr P.fits.Lam rfl hec (fun i hi => hel i hi)
    (fun i yv a _ _ ha => ?_) (fun i yv a hi _ ha => ?_)
  · obtain rfl := Option.some.inj ha
    exact Aff.value_ofConst ρ W _
  · have hi' : i < D.nl := hi
    have ha' : p.v.SxsA wh "Y" (2 * i + 1) = some a := ha
    show a.value ρ W = ∑ x ∈ range D.d,
      Inst.Model.FFSeg.ew D z (if (2 * i + 1) % 2 = 0 then Fam.N1 else Fam.N2) x *
        xU D t (2 * i + 1) x zh
    rw [P.Sxs2 hW (by omega) ha', if_neg (by omega)]
    exact sum_congr rfl fun x hx => by rw [← (hE ew hew).2 x (mem_range.mp hx)]

/-- THE PANEL OF XR: as sides_N1, with the two ties of shareP_XR. -/
theorem sides_XR (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.XR)) (hE : EwTie ρ v D z Fam.XR) (p : PanelEnv)
    (hp : p.v = v) {ec : E} (hec : ρ.val ec = wc D z (call Fam.XR)) (s : Panels)
    (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "XR" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b .XR := by
  subst hp
  rw [panelT_XR_eq, P.fits.p3] at hs
  obtain ⟨ew, hew, e⟩ := of_bind_some (o := p.v.ewOf "XR") hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  obtain ⟨ten, bt, hX, T, R⟩ := P.short2 .m rfl
  refine sides_blk_forms (pn := .XR) rfl rfl rfl hr P.fits.LamM rfl hec
    (fun i hi => hel (2 * i + 1) (odd_lt D hi))
    (fun i yv a _ _ ha => ?_) (fun i yv a _ _ ha => ?_)
  · obtain rfl := Option.some.inj ha
    show (Aff.ofConst (p.shownT.getD (p.v.y.NN * p.v.y.Lam + (2 * i + 1) / 2) zeroE)).value ρ W =
      ρ.val (p.shownT.getD (p.v.y.NN * p.v.y.Lam + i) zeroE)
    rw [Aff.value_ofConst, show (2 * i + 1) / 2 = i by omega]
  · have ha' : p.v.shSum ew p.v.y.h.d "m" "rt" (2 * i + 1) = some a := ha
    show a.value ρ W = ∑ x ∈ range D.d,
      Inst.Model.FFSeg.ew D z Fam.XR x * valU D t .m (2 * i + 1) x zh
    rw [rowXR_value P.fits.num hX T R P.fits.d (2 * i + 1) ha']
    exact sum_congr rfl fun x hx => by rw [← (hE ew hew).2 x (mem_range.mp hx)]

/-- THE PANEL OF DD: as sides_N1, with the two ties of shareP_DD. The sum of the weights of the
segment's entries is a factor of the row's weight, in the verifier's panel and in the library's. -/
theorem sides_DD (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.DD)) (hE : EwTie ρ v D z Fam.DD) (p : PanelEnv)
    (hp : p.v = v) {ec : E} (hec : ρ.val ec = wc D z (call Fam.DD)) (s : Panels)
    (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "DD" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b .DD := by
  subst hp
  rw [panelT_DD_eq, P.fits.p3] at hs
  obtain ⟨ew, hew, e⟩ := of_bind_some (o := p.v.ewOf "DD") hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  have hsw : ρ.val (sumE ew) = Inst.Model.FFSeg.sw D z Fam.DD := by
    rw [sumE_value, (hE ew hew).1]
    exact sum_congr rfl fun x hx => (hE ew hew).2 x (mem_range.mp hx)
  refine sides_blk_forms (pn := .DD) rfl rfl rfl hr P.fits.LamM P.fits.NE hec
    (fun i hi => ?_) (fun i e a _ _ ha => ?_) (fun i e a _ _ ha => ?_)
  · show ρ.val (mulE ((eqTab (p.v.zl q)).getD (2 * i + 1) zeroE) (sumE ew)) =
      Inst.Model.FFSeg.el D z (call Fam.DD) (2 * i + 1) * Inst.Model.FFSeg.sw D z Fam.DD
    rw [ρ.mul, hel (2 * i + 1) (odd_lt D hi), hsw]
  · obtain rfl := Option.some.inj ha
    show (Aff.ofConst (p.shownT.getD
        (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + (2 * i + 1) / 2 * p.v.y.h.NE + e) zeroE)).value ρ W =
      ρ.val (p.shownT.getD (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + i * p.v.y.h.NE + e) zeroE)
    rw [Aff.value_ofConst, show (2 * i + 1) / 2 = i by omega]
  · have ha' : p.v.shA "lr" "rt" ((2 * i + 1) / 2) e = some a := ha
    show a.value ρ W = valU D t .lr i e zh
    rw [P.shA2 .lr rfl rfl ha', show (2 * i + 1) / 2 = i by omega]

/-- THE PANEL OF MR: as sides_N1, with the two ties of shareP_MR. The weight of the segment's one
entry is a factor of the row's weight, in the verifier's panel and in the library's. -/
theorem sides_MR (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.MR)) (hE : EwTie ρ v D z Fam.MR) (p : PanelEnv)
    (hp : p.v = v) {ec : E} (hec : ρ.val ec = wc D z (call Fam.MR)) (s : Panels)
    (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s' : Panels} {b : SBlk}
    (hs : panelT p ec (eqTab (v.zl q)) "MR" s = some s') (hb : s'.bl = s.bl.push b)
    (hr : Returns b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b .MR := by
  subst hp
  rw [panelT_MR_eq, P.fits.p3] at hs
  obtain ⟨ew, hew, e⟩ := of_bind_some (o := p.v.ewOf "MR") hs
  rw [e, plain_push] at hb
  have eb := push_same hb
  subst eb
  have hsw : ρ.val (ew.getD 0 zeroE) = Inst.Model.FFSeg.ew D z Fam.MR 0 :=
    (hE ew hew).2 0 Nat.one_pos
  refine sides_blk_forms (pn := .MR) rfl rfl rfl hr P.fits.LamM P.fits.NE hec
    (fun i hi => ?_) (fun i e a _ _ ha => ?_) (fun i e a _ _ ha => ?_)
  · show ρ.val (mulE ((eqTab (p.v.zl q)).getD (2 * i + 1) zeroE) (ew.getD 0 zeroE)) =
      Inst.Model.FFSeg.el D z (call Fam.MR) (2 * i + 1) * Inst.Model.FFSeg.ew D z Fam.MR 0
    rw [ρ.mul, hel (2 * i + 1) (odd_lt D hi), hsw]
  · obtain rfl := Option.some.inj ha
    show (Aff.ofConst (p.shownT.getD
        (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + (2 * i + 1) / 2 * p.v.y.h.NE + e) zeroE)).value ρ W =
      ρ.val (p.shownT.getD (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + i * p.v.y.h.NE + e) zeroE)
    rw [Aff.value_ofConst, show (2 * i + 1) / 2 = i by omega]
  · have ha' : p.v.shA "lr" "rt" ((2 * i + 1) / 2) e = some a := ha
    show a.value ρ W = valU D t .lr i e zh
    rw [P.shA2 .lr rfl rfl ha', show (2 * i + 1) / 2 = i by omega]

/-! ## The three kinds with the selector -/

/-- THE PANEL GR OF LAYER 2 lm + 1. If the step of panelT for the segment G and that layer returns
(triStep), with the layers' weights in the point of call number q and a call's weight ec that reads
as the library's, and b is the panel that it has appended, then b has the bits of the library's
panel Gr lm, its A side at the record rPort, and the B side 0. Asked beside: PortFits, the tie of
shareP_Gr, and that lm is below the number of layers with routed experts. -/
theorem sides_Gr (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.G)) (p : PanelEnv) (hp : p.v = v) {ec : E}
    (hec : ρ.val ec = wc D z (call Fam.G)) (s : Panels) (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) {s' : Panels} {b : SBlk} {lm : ℕ} (hlm : lm < D.ne)
    (hs : triStep p ec (eqTab (v.zl q)) "G" s lm = some s') (hb : s'.bl = s.bl.push b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b (.Gr lm) := by
  subst hp
  obtain ⟨xx, hxx, e⟩ := of_bind_some
    (o := (Array.range p.v.y.h.d).mapM fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) hs
  rw [e, tri_push] at hb
  have eb := push_same hb
  subst eb
  have hl := odd_lt D hlm
  refine sides_blk_tri (pn := .Gr lm) rfl rfl rfl P.fits.NE P.fits.d hec fun i yv hi hy => ?_
  have hi' : i < p.v.y.h.NE := by
    rw [P.fits.NE]
    exact hi
  have hy' : yv < p.v.y.h.d := by
    rw [P.fits.d]
    exact hy
  show ρ.val (mulE ((eqTab (p.v.zl q)).getD (2 * lm + 1) zeroE)
        (Model.Layer.pw (Model.Layer.tOf (p.v.sc.klM (p.v.lay (2 * lm + 1)) 1)))) *
      ρ.val (((Array.range p.v.y.h.NE).map fun e => p.shownT.getD
        (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE).getD i zeroE) *
      (xx.getD yv {}).value ρ W =
    Inst.Model.Site.scl (D.Pl (2 * lm + 1)).kg'
        (Inst.Model.FFSeg.el D z (call Fam.G) (2 * lm + 1)) *
      (ρ.val (p.shownT.getD (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + i) zeroE) *
        valU D t .xr lm yv zh)
  rw [P.fits.kgR (2 * lm + 1) hl (by omega), scl_weight P.fits.num, hel _ hl,
    range_map_getD _ _ hi', P.shA2 .xr rfl rfl
      (show p.v.shA (arrName Arr.xr) "rt" lm yv = some (xx.getD yv {}) from
        range_mapM_get ({} : Aff) hxx hy')]
  ring

/-- THE PANEL UR OF LAYER 2 lm + 1: as sides_Gr, for the segment U. -/
theorem sides_Ur (P : PortFits ρ W v D c t low z zh) {q : ℕ}
    (hel : ElTie ρ v D z q (call Fam.U)) (p : PanelEnv) (hp : p.v = v) {ec : E}
    (hec : ρ.val ec = wc D z (call Fam.U)) (s : Panels) (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) {s' : Panels} {b : SBlk} {lm : ℕ} (hlm : lm < D.ne)
    (hs : triStep p ec (eqTab (v.zl q)) "U" s lm = some s') (hb : s'.bl = s.bl.push b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b (.Ur lm) := by
  subst hp
  obtain ⟨xx, hxx, e⟩ := of_bind_some
    (o := (Array.range p.v.y.h.d).mapM fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) hs
  rw [e, tri_push] at hb
  have eb := push_same hb
  subst eb
  have hl := odd_lt D hlm
  refine sides_blk_tri (pn := .Ur lm) rfl rfl rfl P.fits.NE P.fits.d hec fun i yv hi hy => ?_
  have hi' : i < p.v.y.h.NE := by
    rw [P.fits.NE]
    exact hi
  have hy' : yv < p.v.y.h.d := by
    rw [P.fits.d]
    exact hy
  show ρ.val (mulE ((eqTab (p.v.zl q)).getD (2 * lm + 1) zeroE)
        (Model.Layer.pw (Model.Layer.tOf (p.v.sc.klM (p.v.lay (2 * lm + 1)) 2)))) *
      ρ.val (((Array.range p.v.y.h.NE).map fun e => p.shownT.getD
        (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE).getD i zeroE) *
      (xx.getD yv {}).value ρ W =
    Inst.Model.Site.scl (D.Pl (2 * lm + 1)).ku'
        (Inst.Model.FFSeg.el D z (call Fam.U) (2 * lm + 1)) *
      (ρ.val (p.shownT.getD (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + i) zeroE) *
        valU D t .xr lm yv zh)
  rw [P.fits.kuR (2 * lm + 1) hl (by omega), scl_weight P.fits.num, hel _ hl,
    range_map_getD _ _ hi', P.shA2 .xr rfl rfl
      (show p.v.shA (arrName Arr.xr) "rt" lm yv = some (xx.getD yv {}) from
        range_mapM_get ({} : Aff) hxx hy')]
  ring

/-- THE PANEL DR OF LAYER 2 lm + 1. If the step of panelT for the segment D and that layer returns
(triStep), on whatever call's weight ec and layers' weights el, and b is the panel that it has
appended, then b has the bits of the library's panel Dr lm, and both sides are 0: its column factor
is a never-sent vector and its B side a weight matrix. Of PortFits only the numbers of the experts
and of an expert's hidden units are used. -/
theorem sides_Dr (P : PortFits ρ W v D c t low z zh) (p : PanelEnv) (hp : p.v = v) (ec : E)
    (el : Array E) (s : Panels) (hv : ℕ → ℕ → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    {s' : Panels} {b : SBlk} {lm : ℕ} (hs : triStep p ec el "D" s lm = some s')
    (hb : s'.bl = s.bl.push b) :
    SidesAre ρ W v.y om D (rPort ρ v.y p.shownT hv D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b (.Dr lm) := by
  subst hp
  have e : Model.Layer.tri p.v.y ec 1 p.v.y.h.fe
      ((Array.range p.v.y.h.NE).map fun e => p.shownT.getD
        (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE)
      #[] (some (1 + lm))
      (mulE (el.getD (2 * lm + 1) zeroE)
        (kT p.v.sc (p.v.lay (2 * lm + 1)) Model.Layer.Lkd)) s = s' := Option.some.inj hs
  rw [← e, tri_push] at hb
  have eb := push_same hb
  subst eb
  refine sides_virt (pn := .Dr lm) rfl rfl (k := 1 + lm) (v0 := s.nextV) rfl rfl (n := D.nx) rfl
    P.fits.fe rfl ?_
  show ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.fe = ceilLog2 D.nx + ceilLog2 p.v.y.h.fe
  rw [ceil_max_one, P.fits.NE]

end Kinds

/-! ## The eight kinds in one -/

section Whole

variable [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv} {c : ClaimEnv}
  {h : Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim} {lk L0 : ℕ}
  {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- **The eight late kinds other than QK, under SigFits.** If b is the verifier's panel of the
library's panel pn (IsPanelOf), the calls of the second walk are 0, 1, 2, 5, and pn is N1, N2, XR,
DD, MR, or Gr l, Ur l, Dr l for some l, then b has the bits and, side by side, the form parts of pn
at the record rPort. hr: the forms of the sides of b are there, if b is a panel whose sides are read
as forms. hh: the never-sent vectors in the record rPort, free; w: the weights in the library's B
sides, free (no B side of these eight that is a form part reads them). -/
theorem panel_sides_late (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb)
    (hh : ℕ → ℕ → K) (w : ℕ → LW K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {cl : List WsClaim}
    {om : Array E} {b : SBlk} {pn : Pan} (hI : IsPanelOf p c TS cl b pn)
    (hpn : pn = .N1 ∨ pn = .N2 ∨ pn = .XR ∨ pn = .DD ∨ pn = .MR ∨ (∃ l, pn = .Gr l) ∨
      (∃ l, pn = .Ur l) ∨ ∃ l, pn = .Dr l)
    (hr : b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) → Returns b) :
    SidesAre ρ Wo p.v.y om D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0 w z zh
      (ρ.val (om.getD 1 zeroE)) b pn := by
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  cases pn with
  | Gr lm =>
    obtain ⟨_, -, -, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', _, -, -, hlm, -, hstep, hbl, -, -, -⟩ := H
    rw [hTS] at hq
    have hq' : q = (call Fam.G).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hstep
    exact sides_Gr S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) p rfl
      (by rw [hq']; exact S.wc (call Fam.G) (by decide)) st hh tb L0 w
      (by rw [← S.aim.claim.LamM, ← S.env]; exact hlm) hstep hbl
  | Ur lm =>
    obtain ⟨_, -, -, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', _, -, -, hlm, -, hstep, hbl, -, -, -⟩ := H
    rw [hTS] at hq
    have hq' : q = (call Fam.U).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hstep
    exact sides_Ur S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) p rfl
      (by rw [hq']; exact S.wc (call Fam.U) (by decide)) st hh tb L0 w
      (by rw [← S.aim.claim.LamM, ← S.env]; exact hlm) hstep hbl
  | Dr lm =>
    obtain ⟨_, -, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, st', _, -, -, -, -, hstep, hbl, -, -, -⟩ := H
    rw [hn] at hstep
    exact sides_Dr S.port p rfl _ _ st hh tb L0 w hstep hbl
  | N1 =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.N1).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨-, f2⟩ := facts_N1 hs hbl
    exact sides_N1 S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
      (S.wts _ (by simp)) p rfl (by rw [hq']; exact S.wc (call Fam.N1) (by decide)) st hh tb L0 w
      hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k)
  | N2 =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.N2).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨-, f2⟩ := facts_N2 hs hbl
    exact sides_N2 S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
      (S.wts _ (by simp)) p rfl (by rw [hq']; exact S.wc (call Fam.N2) (by decide)) st hh tb L0 w
      hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k)
  | XR =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.XR).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨-, f2⟩ := facts_XR h3 hs hbl
    exact sides_XR S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
      p rfl (by rw [hq']; exact S.wc (call Fam.XR) (by decide)) st hh tb L0 w
      hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k)
  | DD =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.DD).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨-, f2⟩ := facts_DD h3 hs hbl
    exact sides_DD S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
      p rfl (by rw [hq']; exact S.wc (call Fam.DD) (by decide)) st hh tb L0 w
      hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k)
  | MR =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.MR).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨-, f2⟩ := facts_MR h3 hs hbl
    exact sides_MR S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
      p rfl (by rw [hq']; exact S.wc (call Fam.MR) (by decide)) st hh tb L0 w
      hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k)
  | _ => simp at hpn

end Whole

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sides_N1
#print axioms OnBytes.Road.K4.sides_N2
#print axioms OnBytes.Road.K4.sides_XR
#print axioms OnBytes.Road.K4.sides_DD
#print axioms OnBytes.Road.K4.sides_MR
#print axioms OnBytes.Road.K4.sides_Gr
#print axioms OnBytes.Road.K4.sides_Ur
#print axioms OnBytes.Road.K4.sides_Dr
#print axioms OnBytes.Road.K4.panel_sides_late
