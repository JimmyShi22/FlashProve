-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlacesTies.lean

The places of Johnson/HonestTrace/Places.lean against this library's Lean text on the verifier's
side: the planes of the lookups' counts, the layers, attention.

"The verifier" in this file is the Lean verifier under OnBytes/Model/.
Johnson/HonestTrace/Places.lean writes the byte format's rules for shapes and places over a
structure of numbers "Sz", typed from the format's pages. Of that file's theorems only "ref_cols"
and "small_cols" hold a number or a rule against the example sets' files (through numbers typed by
hand), and only the columns; rows, places and owners are held against nothing there. Here the
numbers are taken from the parameter file's lines as the verifier's reader holds them ("Model.Hdr",
OnBytes/Model/Config.lean), and shapes and places are compared with what the verifier's layout
functions return and with the rules by which the files of Johnson/Road/ and OnBytes/Tie/ read a cell
in the verifier's lists. "Profile 4" is the parameter file's line prof 20 ("Shape.p4").

Main definitions and theorems:
* "Sz.ofHdr": the numbers at a parameter file's lines; the lookups' kT and NC are arguments.
* The planes. "atBit_cellRC": if a lookup's kT is S's, 5 ≤ lm ≤ kT + 5 and j < 32, the row and
  column of a bit are "FoNums.cellRC". "k_b_of_layout", "k_bA_of_shapeHid", "k_bH_of_layout": if
  "Layer.layout", "Attention.shapeHid", "Head.layout" return, and the line lm and the returned
  lookup's kT and NC are S's, then S's number of columns of b, bA, bH is the returned one.
* The layers. "FitsL"; "fitsL_ofHdr": it holds of "Sz.ofHdr" and the verifier's "layerShape".
  "place_eq_placeOf": under "Sz.OK", "Laid2", "Switches", "FitsL" and profile 4, in a group below
  nGr, the number in the list, the row and the column of a valid feed-forward name's place are
  "placeOf" (Johnson/Road/FormsKeysAddr.lean). "place_eq_placeOf_of_layout": at "Sz.ofHdr", for
  every layout that "Layer.layout" returns at "layerShape"; "Sz.OK", "Switches", profile 4 and the
  group below nGr stay premises.
* Attention. "FitsA", "FitsCf". "fitsCf_of_fill": what "Attention.fill" returns meets "FitsCf" at
  "Sz.ofHdr", if the layout meets "Laid2", holds "layerShape" and has ldh as "ldh_of_layout" says.
  "fitsA_of_shaped": under "Sz.OK", "Sz.Fit" and "FitsCf", a shape with "L5.Shaped" meets "FitsA".
  "place_eq_addrA": under "Sz.OK", "Sz.Fit", "L5.Norm" and "FitsA", in a group below nGr, for a
  valid name of attention, own or borrowed, the number in the attention segment's list, the row and
  the column of its place are "L5.addrA" (Johnson/Road/Lane5AttDef.lean).
  "place_eq_addrA_of_group": at "Sz.ofHdr", for the plan that "Attention.group" returns at a layout
  that "Layer.layout" returns at "layerShape"; "Sz.OK", "Sz.Fit" and the group below nGr stay
  premises.
* The head. "fitsH_ofHdr": "FitsH" of Johnson/HonestTrace/PlacesTiesHead.lean holds of "Sz.ofHdr"
  and the verifier's "headShape".

Limits. "placeOf", "L5.addrA" and "FoNums.cellRC" are functions of this library beside the Lean
verifier, not parts of its text, and not the C++ verifier's. "placeOf" is the rule of "cellsAt"
(Johnson/Road/FormsKeysMat.lean). Of "L5.addrA" its own file says that it is written by a reading of
the verifier's texts, and that no theorem ties it to them. "FoNums.cellRC" is typed after the
verifier's "planesAt" (OnBytes/Tie/Pv/Lookup/Port/FoNums.lean). "Sz.OK" and "Sz.Fit" stay premises
at "Sz.ofHdr": this file does not show them from "the layout functions return". The lookups' kT and
NC are premises of the planes' theorems; they hold by definition if the caller fills "Sz.ofHdr" with
the returned lookups' numbers at the segments of the proof, and "Sz.OK" asks nothing of them
elsewhere. The layers' tie asks the digit forms and switches of "Switches" and profile 4. No theorem
of this file shows that the premises hold together anywhere: that "Layer.layout", "Attention.group"
or "Attention.shapeHid" return for some file, with "Switches" and profile 4. No theorem here reads a
parameter file: that "Sz.ref" or "Sz.small" is "Sz.ofHdr" at an example's file is not shown.

Not claimed: that a prover lays its cells at these places; that a verifier accepts anything;
anything on the values of the cells.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import Johnson.Desc.First.Att.Claims.PlanesHost
import Johnson.Road.HeadLaid
import Johnson.Road.FormsKeysAddr
import Johnson.Road.Lane5AttNum
import Johnson.Road.FormsKeysCap
import Johnson.Flat.Instance
import Johnson.HonestTrace.Counts
import Johnson.HonestTrace.PlacesBack
import Johnson.HonestTrace.PlacesTiesHead

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Model (Forest.Shape)

/-! ## The planes -/

/-- What "Forest.planeCols" has tested where it returns, and what it returns. -/
theorem planeCols_ok {h : Forest.Shape} {lm k : ℕ} (e : Model.Forest.planeCols h lm = .ok k) :
    5 ≤ lm ∧ lm ≤ h.kT + 5 ∧ k = h.NC * 2 ^ (h.kT + 5 - lm) := by
  unfold Model.Forest.planeCols at e
  split at e
  · cases e
  · rename_i hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hn
    exact ⟨hn.1, hn.2, (Except.ok.inj e).symm⟩

/-- If the lookup's kT is S's for the segment σ, 5 ≤ lm ≤ kT + 5 and j < 32: the row and the column
of the place of the bit (t, c, j) are "FoNums.cellRC" at lm. -/
theorem atBit_cellRC (S : Sz) (σ : Seg) (h : Forest.Shape) (hk : h.kT = S.kT σ)
    (h5 : 5 ≤ S.lmP σ) (hlm : S.lmP σ ≤ S.kT σ + 5) (t c : ℕ) {j : ℕ} (hj : j < 32) :
    ((S.atBit σ t c j).2.2.1, (S.atBit σ t c j).2.2.2) = FoNums.cellRC h (S.lmP σ) (t, c, j) := by
  rw [cellRC_flat h (S.lmP σ) h5 (by rw [hk]; exact hlm) t c hj, hk]
  rfl

/-- If the lookup's kT and NC are S's for the segment σ and "Forest.planeCols" returns k at S's lm:
S's number of columns of the planes is k, and 5 ≤ lm ≤ kT + 5. -/
theorem kP_of_planeCols (S : Sz) (σ : Seg) (h : Forest.Shape) (hk : h.kT = S.kT σ)
    (hn : h.NC = S.NC σ) {k : ℕ} (e : Model.Forest.planeCols h (S.lmP σ) = .ok k) :
    S.kP σ = k ∧ 5 ≤ S.lmP σ ∧ S.lmP σ ≤ S.kT σ + 5 := by
  obtain ⟨h1, h2, h3⟩ := planeCols_ok e
  rw [hk] at h2 h3
  rw [hn] at h3
  exact ⟨h3.symm, h1, h2⟩

/-- If "Layer.layout" returns y, and y's line lmb and its lookup's kT and NC are S's for group g:
S's number of columns of b is y.kbm. -/
theorem k_b_of_layout (S : Sz) (g : ℕ) {hL : Model.Layer.Shape} {pc : List (List String)}
    {y : Model.Layer.Lay} (hy : Model.Layer.layout hL pc = .ok y) (hlm : S.lmb = y.h.lmb)
    (hk : y.fo.kT = S.kT (.ff g)) (hn : y.fo.NC = S.NC (.ff g)) :
    S.k (.ff g) .b = y.kbm := by
  rw [Fo.PlaneMatG.layout_kbm hy]
  show S.NC (.ff g) * 2 ^ (S.kT (.ff g) + 5 - S.lmb) = y.fo.NC * 2 ^ (y.fo.kT + 5 - y.h.lmb)
  rw [hlm, hk, hn]

/-- If "Attention.shapeHid" returns (A, fs) at the configuration cf, and cf's lmb and fs's kT and NC
are S's for group g: S's number of columns of bA is A.kbA. -/
theorem k_bA_of_shapeHid (S : Sz) (g : ℕ) {lid : ℕ} {cf : Attention.Cfg} {A : Attention.Shape}
    {fs : Forest.Shape} (hA : Attention.shapeHid lid cf = .ok (A, fs)) (hlm : S.lmbA = cf.lmb)
    (hk : fs.kT = S.kT (.att g)) (hn : fs.NC = S.NC (.att g)) :
    S.k (.att g) .bA = A.kbA :=
  (kP_of_planeCols S (.att g) fs hk hn
    (by rw [show S.lmP (.att g) = cf.lmb from hlm]; exact K5Law.kb_of_hid hA)).1

/-- If "Head.layout" returns L at the shape hH, and hH's lmbH and the kT and NC of L's lookup are
S's: S's number of columns of bH is L.kb. -/
theorem k_bH_of_layout (S : Sz) {hH : Model.Head.Shape} {tau : Array UInt64} {L : Model.Head.HL}
    (hy : Model.Head.layout hH tau = .ok L) (hlm : S.lmbH = hH.lmbH)
    (hk : L.fs.kT = S.kT .head) (hn : L.fs.NC = S.NC .head) :
    S.k .head .bH = L.kb := by
  unfold Model.Head.layout at hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨calls, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨kb, h9, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  cases hy
  exact (kP_of_planeCols S .head fs hk hn (by rw [show S.lmP .head = hH.lmbH from hlm]; exact h9)).1

/-! ## The sizes, from the parameter file's lines -/

/-- **The numbers at the lines of a parameter file**, as the Lean verifier's reader holds them. A
matrix of features with the line lm has 2^lm / 2^lt features in a column, as in the verifier's
layout functions; at lm < lt that is 0. The model's sizes are "Flat.sizesOf". u0 and the lookups' kT
and NC are no lines of the file, and are arguments. -/
def Sz.ofHdr (h : Model.Hdr) (u0 : ℕ) (kT NC : Seg → ℕ) : Sz :=
  { P := Flat.sizesOf h
    lt := h.lt, ll := h.ll, nGr := h.L / 2 ^ h.ll, lg := Model.clog2 h.Gk, lB := h.lB,
    ln := ceilLog2 h.dh, u0 := u0, la := h.la,
    wcaf := 2 ^ h.lmaf / 2 ^ h.lt, NAf := h.NAf, wcad := 2 ^ h.lmad / 2 ^ h.lt, NAd := h.NAd,
    wcar := 2 ^ h.lmar / 2 ^ h.lt, lmb := h.lmb, wcq := 2 ^ h.lmq / 2 ^ h.lt,
    wcx := 2 ^ h.lmx / 2 ^ h.lt, lmS := h.lmS, NAs := h.NAs, wch := 2 ^ h.lmh / 2 ^ h.lt,
    wco := 2 ^ h.lmo / 2 ^ h.lt, lmbA := h.lmbA, wchf := 2 ^ h.lmhf / 2 ^ h.lt, NHf := h.NHf,
    wchd := 2 ^ h.lmhd / 2 ^ h.lt, wchr := 2 ^ h.lmhr / 2 ^ h.lt, lmbH := h.lmbH,
    kT := kT, NC := NC }

/-! ## The layers -/

section Layers
open OnBytes.Road
open OnBytes.Model.Layer (Lay matIx)
open Inst.Model.FFSeg.IndexFacts (feat_lt mx_ne_b)

/-- The numbers of S that a feed-forward segment's places read are those of the layers' shape h. -/
structure FitsL (S : Sz) (h : Model.Layer.Shape) : Prop where
  lt : S.lt = h.lt
  wcaf : S.wcaf = 2 ^ h.lmaf / 2 ^ h.lt
  NAf : S.NAf = h.NAf
  wcad : S.wcad = 2 ^ h.lmad / 2 ^ h.lt
  NAd : S.NAd = h.NAd
  wcar : S.wcar = 2 ^ h.lmar / 2 ^ h.lt
  wcq : S.wcq = 2 ^ h.lmq / 2 ^ h.lt
  wcx : S.wcx = 2 ^ h.lmx / 2 ^ h.lt
  sized : Sized h S.DF

/-- "FitsL" holds of the numbers at a parameter file's lines and the layers' shape that the Lean
verifier makes of that file ("layerShape"). By definition. -/
theorem fitsL_ofHdr (P : Model.PolScan) (u0 : ℕ) (kT NC : Seg → ℕ) :
    FitsL (Sz.ofHdr P.h u0 kT NC) (Model.Verify.layerShape P) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

variable {S : Sz} {y : Lay}

/-- Under "Laid2" and "FitsL" the layout's positions are 2^lt. -/
theorem T_of_fitsL (L : Laid2 y) (F : FitsL S y.h) : y.T = 2 ^ S.lt := by rw [L.T, F.lt]

/-- Under "Laid2" and "FitsL": the features in a column, as the layout's rows and positions give
them, are S's, for the six matrices that hold cells. -/
theorem fcM_of_fitsL (L : Laid2 y) (F : FitsL S y.h) {μ : FFSeg.Mx} (hμ : μ ≠ .b) :
    fcM y (mxNo μ) = S.wc (famOf μ) := by
  cases μ with
  | b => exact absurd rfl hμ
  | af => show y.mrow.getD 0 0 / y.T = S.wcaf; rw [L.mrow0, L.T, F.wcaf]
  | ad => show y.mrow.getD 1 0 / y.T = S.wcad; rw [L.mrow1, L.T, F.wcad]
  | ar => show y.mrow.getD 2 0 / y.T = S.wcar; rw [L.mrow2, L.T, F.wcar]
  | qa => show y.mrow.getD 3 0 / y.T = S.wcq; rw [L.mrow3, L.T, F.wcq]
  | xin => show y.mxb / y.T = S.wcx; rw [L.mxb, L.T, F.wcx]
  | xout => show y.mxb / y.T = S.wcx; rw [L.mxb, L.T, F.wcx]

/-- x rounded up to a multiple of w, by w, is x / w rounded up; also at w = 0, where both are 0. -/
theorem roundUp_div' (x w : ℕ) : Model.roundUp x w / w = Sz.ceilDiv x w := by
  rcases Nat.eq_zero_or_pos w with h | h
  · subst h
    simp [Sz.ceilDiv]
  · exact roundUp_div x h

/-- Under "Laid2", "Switches", "FitsL" and profile 4: the layout's columns of a part are S's, for
the six matrices that hold cells. -/
theorem colsM_of_fitsL (L : Laid2 y) (Sw : Switches y.h) (F : FitsL S y.h)
    (hp4 : y.h.p4 = true) {μ : FFSeg.Mx} (hμ : μ ≠ .b) :
    colsM y (mxNo μ) = S.kF (famOf μ) := by
  obtain ⟨t0, t1, t2, t3, -, t4, t5⟩ := feat_total L Sw F.sized
  cases μ with
  | b => exact absurd rfl hμ
  | af =>
    show y.kcol.getD 0 0 = Sz.ceilDiv (FFSeg.nFeatMx S.DF .af) (S.NAf * S.wcaf)
    rw [L.kcol0, roundUp_div', ← L.feat0, t0, F.NAf, F.wcaf]
  | ad =>
    show y.kcol.getD 1 0 = Sz.ceilDiv (FFSeg.nFeatMx S.DF .ad) (S.NAd * S.wcad)
    rw [L.kcol1, roundUp_div', ← L.feat1, t1, F.NAd, F.wcad]
  | ar =>
    show y.kcol.getD 2 0 = Sz.ceilDiv (FFSeg.nFeatMx S.DF .ar) (1 * S.wcar)
    rw [L.kcol2, roundUp_div', ← L.feat2, t2, F.wcar]
  | qa =>
    show y.kcol.getD 3 0 = Sz.ceilDiv (FFSeg.nFeatMx S.DF .qa) (1 * S.wcq)
    rw [L.kcol3, roundUp_div', ← L.feat3, t3 hp4, F.wcq]
  | xin =>
    show y.kxb = Sz.ceilDiv (FFSeg.nFeatMx S.DF .xin) (1 * S.wcx)
    rw [L.kxb, roundUp_div', t4, F.wcx, Nat.one_mul]
  | xout =>
    show y.kxb = Sz.ceilDiv (FFSeg.nFeatMx S.DF .xout) (1 * S.wcx)
    rw [L.kxb, roundUp_div', t5, F.wcx, Nat.one_mul]

/-- Under "Laid2" and "FitsL", in a group below nGr, for the six matrices that hold cells and p
below the number of parts: S's number of part p of a matrix is the number of the matrix's first part
in the verifier's list ("matIx") plus p. -/
theorem mu_firstM (L : Laid2 y) (F : FitsL S y.h) {g : ℕ} (hg : g < S.nGr) {μ : FFSeg.Mx}
    (hμ : μ ≠ .b) {p : ℕ} (hp : p < S.np (famOf μ)) :
    S.mu (.ff g) ((famOf μ).setPart p) = some (firstM y (mxNo μ) + p) := by
  unfold Sz.mu
  rw [if_pos (show (Seg.ff g).Below S.nGr from hg)]
  have e0 := L.parts0
  have e1 := L.parts1
  cases μ with
  | b => exact absurd rfl hμ
  | af =>
    have hp' : p < S.NAf := hp
    show (if p < S.NAf then some p else none) = some (0 + p)
    rw [if_pos hp', Nat.zero_add]
  | ad =>
    have hp' : p < S.NAd := hp
    show (if p < S.NAd then some (S.NAf + p) else none) = some (y.parts.getD 0 0 + p)
    rw [if_pos hp', e0, F.NAf]
  | ar =>
    have hp' : p < 1 := hp
    show some (S.NAf + S.NAd) = some (y.parts.getD 0 0 + y.parts.getD 1 0 + p)
    rw [e0, e1, F.NAf, F.NAd, show p = 0 by omega]
    rfl
  | qa =>
    have hp' : p < 1 := hp
    show some (S.NAf + S.NAd + 2) = some (y.parts.getD 0 0 + y.parts.getD 1 0 + 2 + p)
    rw [e0, e1, F.NAf, F.NAd, show p = 0 by omega]
  | xin =>
    have hp' : p < 1 := hp
    show some (S.NAf + S.NAd + 4) = some (y.parts.getD 0 0 + y.parts.getD 1 0 + 4 + p)
    rw [e0, e1, F.NAf, F.NAd, show p = 0 by omega]
  | xout =>
    have hp' : p < 1 := hp
    show some (S.NAf + S.NAd + 3) = some (y.parts.getD 0 0 + y.parts.getD 1 0 + 3 + p)
    rw [e0, e1, F.NAf, F.NAd, show p = 0 by omega]

/-- **The layers.** Under "Sz.OK", "Laid2", "Switches", "FitsL" and profile 4, in a group below nGr:
the number in the list, the row and the column of a valid feed-forward name's place are "placeOf".
Unlike the theorems on "placeOf" in Johnson/Road/FormsKeysAddr.lean it does not ask "Sized2" (lmaf =
lmq = lmx, one part of ad). -/
theorem place_eq_placeOf (h : S.OK) (L : Laid2 y) (Sw : Switches y.h) (F : FitsL S y.h)
    (hp4 : y.h.p4 = true) {g : ℕ} (hg : g < S.nGr) (q : FFSeg.Cell) (hv : q.Valid S.DF) :
    S.mu (.ff g) ((Name.ff g q).place S).2.1 = some (placeOf y S.DF q).1 ∧
      ((Name.ff g q).place S).2.2.1 = (placeOf y S.DF q).2.1 ∧
      ((Name.ff g q).place S).2.2.2 = (placeOf y S.DF q).2.2 := by
  have hμ := mx_ne_b q.X
  have hφ : FFSeg.feat S.DF q.X q.k q.inst q.j < S.n (famOf q.X.mx) := by
    rw [Sz.n_famOf]
    exact feat_lt S.DF hv.1 hv.2.1 hv.2.2.1
  have hp := (Sz.part_lt h (Sz.isFeat_famOf g hμ) hφ).1
  unfold placeOf
  rw [fcM_of_fitsL L F hμ, colsM_of_fitsL L Sw F hp4 hμ, T_of_fitsL L F]
  exact ⟨mu_firstM L F hg hμ hp, rfl, rfl⟩

end Layers

/-! ## Attention -/

section Attention
open OnBytes.Road
open Inst.Model.AttSeg.AddrFacts (adr phi pos mat SM SD Phi IsC phi_lt adr_lt)

/-- The numbers of an attention shape that a place reads are those of S. The library's sizes are
compared but for u0, which no place reads. -/
structure FitsA (S : Sz) (A : Attention.Shape) : Prop where
  dim : { L5.dimOf A with u0 := S.u0 } = S.DA
  T : A.T = 2 ^ S.lt
  NAs : A.cf.NAs = S.NAs
  lmS : A.cf.lmS = S.lmS
  kAs : A.kAs / A.cf.NAs = S.kF (.as 0)
  wcH : A.cf.wcH = S.wch
  wcO : A.cf.wcO = S.wco
  wcQ : A.cf.wcQ = S.wcq

/-- The number of a cell of as does not read u0. -/
theorem adr_u0 (D : AttSeg.Dim) (u : ℕ) (ρ : AttSeg.Reg) (jj b x : ℕ) :
    adr { D with u0 := u } ρ jj b x = adr D ρ jj b x := by cases ρ <;> rfl

/-- The number of a feature of attention does not read u0. -/
theorem phi_u0 (D : AttSeg.Dim) (u : ℕ) (c : AttSeg.Raw) : phi { D with u0 := u } c = phi D c := by
  cases c <;> rfl

variable {S : Sz} {A : Attention.Shape}

/-- Under "Sz.OK" and "FitsA", for a matrix of features in one part with the number a in the
attention segment's list and wcA features in a column: the place of a feature in use is
"L5.featCell". -/
theorem tie_feat (h : S.OK) (F : FitsA S A) {g : ℕ} {σ : Seg} {μ : MatName} {a wcA : ℕ}
    (hf : isFeat σ μ = true) (h1 : S.np μ = 1) (hs : ∀ p, μ.setPart p = μ)
    (hmu : S.mu (.att g) μ = some a) (hw : wcA = S.wc μ) {φ : ℕ} (i : ℕ) (hφ : φ < S.n μ) :
    S.mu (.att g) (S.atFeat σ μ φ i).2.1 = some (L5.featCell A a wcA φ i).1 ∧
      (S.atFeat σ μ φ i).2.2.1 = (L5.featCell A a wcA φ i).2.1 ∧
      (S.atFeat σ μ φ i).2.2.2 = (L5.featCell A a wcA φ i).2.2 := by
  subst hw
  obtain ⟨hp, hc⟩ := Sz.part_lt h hf hφ
  rw [h1] at hp
  have hk : 0 < S.kF μ := Nat.lt_of_le_of_lt (Nat.zero_le _) hc
  have hlt : φ / S.wc μ < S.kF μ := by
    have := (Nat.div_lt_iff_lt_mul hk).1 hp
    omega
  refine ⟨?_, ?_, ?_⟩
  · show S.mu (.att g) (μ.setPart _) = some a
    rw [hs, hmu]
  · show φ % S.wc μ * 2 ^ S.lt + i = φ % S.wc μ * A.T + i
    rw [F.T]
  · show φ / S.wc μ % S.kF μ = φ / S.wc μ
    exact Nat.mod_eq_of_lt hlt

/-- "L5.addrL" at a name that is no cell of an entry, by the name's matrix. -/
theorem addrL_of_mat {c : AttSeg.Raw} (hC : ¬ IsC c) :
    L5.addrL A c =
      match mat c with
      | .ah => L5.featCell A A.cf.NAs A.cf.wcH (phi (L5.dimOf A) c) (pos c)
      | .ao => L5.featCell A (A.cf.NAs + 1) A.cf.wcO (phi (L5.dimOf A) c) (pos c)
      | _ => L5.featCell A (A.cf.NAs + 3) A.cf.wcQ (phi (L5.dimOf A) c) (pos c) := by
  cases c <;> first | exact absurd trivial hC | rfl

/-- The place of a name of attention that is no cell of an entry, own or borrowed, by the name's
matrix. -/
theorem place_att_any (g : ℕ) {c : AttSeg.Raw} (hC : ¬ IsC c) :
    (mat c = .ah ∧ (Name.att g c).place S = S.atFeat (.att g) .ah (phi S.DA c) (pos c)) ∨
      (mat c = .ao ∧ (Name.att g c).place S = S.atFeat (.att g) .ao (phi S.DA c) (pos c)) ∨
      (mat c = .qa ∧ (Name.att g c).place S = S.atFeat (.ff g) .qa (phi S.DA c) (pos c)) := by
  cases c <;>
    first
      | exact absurd trivial hC
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Under "Sz.OK", "Sz.Fit" and "FitsA", in a group below nGr, for a valid name of attention, own or
borrowed: the number in the attention segment's list of the matrix in which it is laid, the row and
the column are "L5.addrL". -/
theorem place_eq_addrL (h : S.OK) (f : S.Fit) (F : FitsA S A) {g : ℕ}
    (hg : g < S.nGr) (c : AttSeg.Raw) (hv : c.Valid S.DA) :
    S.mu (.att g) ((Name.att g c).place S).2.1 = some (L5.addrL A c).1 ∧
      ((Name.att g c).place S).2.2.1 = (L5.addrL A c).2.1 ∧
      ((Name.att g c).place S).2.2.2 = (L5.addrL A c).2.2 := by
  have hb : (Seg.att g).Below S.nGr := hg
  have ep : phi (L5.dimOf A) c = phi S.DA c := by
    have e := phi_u0 (L5.dimOf A) S.u0 c
    rw [F.dim] at e
    exact e.symm
  by_cases hC : IsC c
  · cases c with
    | c ρ jj b x =>
      have ea : adr (L5.dimOf A) ρ jj b x = adr S.DA ρ jj b x := by
        have e := adr_u0 (L5.dimOf A) S.u0 ρ jj b x
        rw [F.dim] at e
        exact e.symm
      have hp := (Sz.atCell_lt h (adr_lt S.DA hv)).1
      show S.mu (.att g) (.as (adr S.DA ρ jj b x / 2 ^ S.lmS / S.kF (.as 0))) =
          some (L5.asCell A (adr (L5.dimOf A) ρ jj b x)).1 ∧
        adr S.DA ρ jj b x % 2 ^ S.lmS = (L5.asCell A (adr (L5.dimOf A) ρ jj b x)).2.1 ∧
        adr S.DA ρ jj b x / 2 ^ S.lmS % S.kF (.as 0) =
          (L5.asCell A (adr (L5.dimOf A) ρ jj b x)).2.2
      unfold L5.asCell
      rw [ea, F.lmS, F.kAs]
      refine ⟨?_, rfl, rfl⟩
      unfold Sz.mu
      rw [if_pos hb]
      exact if_pos hp
    | _ => exact False.elim hC
  · have hφ := (phi_lt S.DA c hv hC).1
    have mu1 : S.mu (.att g) .ah = some A.cf.NAs := by
      unfold Sz.mu
      rw [if_pos hb, F.NAs]
      rfl
    have mu2 : S.mu (.att g) .ao = some (A.cf.NAs + 1) := by
      unfold Sz.mu
      rw [if_pos hb, F.NAs]
      rfl
    have mu3 : S.mu (.att g) .qa = some (A.cf.NAs + 3) := by
      unfold Sz.mu
      rw [if_pos hb, F.NAs]
      rfl
    rw [addrL_of_mat hC, ep]
    rcases place_att_any (S := S) g hC with ⟨hm, e⟩ | ⟨hm, e⟩ | ⟨hm, e⟩
    · rw [hm] at hφ ⊢
      rw [e]
      exact tie_feat h F (σ := .att g) rfl rfl (fun _ => rfl) mu1 F.wcH _ hφ
    · rw [hm] at hφ ⊢
      rw [e]
      exact tie_feat h F (σ := .att g) rfl rfl (fun _ => rfl) mu2 F.wcO _ hφ
    · rw [hm] at hφ ⊢
      rw [e]
      rw [Phi_qa f] at hφ
      exact tie_feat h F (σ := .ff g) rfl rfl (fun _ => rfl) mu3 F.wcQ _ hφ

/-- **Attention.** Under "Sz.OK", "Sz.Fit", "L5.Norm" and "FitsA", in a group below nGr, for a valid
name of attention, own or borrowed: the number in the attention segment's list of the matrix in
which it is laid (for a borrowed name: the number of qa), the row and the column are "L5.addrA". -/
theorem place_eq_addrA (h : S.OK) (f : S.Fit) (N : L5.Norm A) (F : FitsA S A) {g : ℕ}
    (hg : g < S.nGr) (c : AttSeg.Raw) (hv : c.Valid S.DA) :
    S.mu (.att g) ((Name.att g c).place S).2.1 = some (L5.addrA A c).1 ∧
      ((Name.att g c).place S).2.2.1 = (L5.addrA A c).2.1 ∧
      ((Name.att g c).place S).2.2.2 = (L5.addrA A c).2.2 := by
  rw [L5.addrA_norm N c]
  exact place_eq_addrL h f F hg c hv

/-- The numbers of S are those of an attention configuration. -/
structure FitsCf (S : Sz) (cf : Attention.Cfg) : Prop where
  lt : cf.lt = S.lt
  lB : cf.lB = S.lB
  lgk : cf.lgk = S.lg
  ldh : cf.ldh = S.ln
  ll : cf.ll = S.ll
  H : cf.H = S.P.nq
  NAs : cf.NAs = S.NAs
  lmS : cf.lmS = S.lmS
  wcH : cf.wcH = S.wch
  wcO : cf.wcO = S.wco
  wcQ : cf.wcQ = S.wcq

/-- Under "Sz.OK" and "Sz.Fit": if the configuration's numbers are S's ("FitsCf"), so are those of a
shape whose fields are the functions of the configuration that "L5.Shaped" lists. -/
theorem fitsA_of_shaped (h : S.OK) (f : S.Fit) {cf : Attention.Cfg} (C : FitsCf S cf)
    (P : L5.Shaped cf A) : FitsA S A := by
  have hB := h.lB
  have hdim : { L5.dimOf A with u0 := S.u0 } = S.DA := by
    show (⟨A.cf.lgk, A.lnT - 1, A.cf.lB, A.cf.ldh, A.HA, A.Lam, S.u0⟩ : AttSeg.Dim) =
      ⟨S.lg, S.lt - 1 - S.lB, S.lB, S.ln, S.P.nq / S.P.nkv, 2 ^ S.ll, S.u0⟩
    rw [P.cfg, P.lnT, P.HA, P.Lam, C.lgk, C.lB, C.ldh, C.ll, C.H, C.lt, f.nkv,
      show S.lt - S.lB - 1 = S.lt - 1 - S.lB by omega]
  refine ⟨hdim, by rw [P.T, C.lt], by rw [P.cfg, C.NAs], by rw [P.cfg, C.lmS], ?_,
    by rw [P.cfg, C.wcH], by rw [P.cfg, C.wcO], by rw [P.cfg, C.wcQ]⟩
  rw [P.kAs, P.cfg, Nat.mul_div_cancel _ (by rw [C.NAs]; exact h.NAs)]
  show _ = Sz.ceilDiv (SM S.DA + SD S.DA) (S.NAs * 2 ^ S.lmS)
  unfold Sz.ceilDiv
  have eM : Attention.nMOf cf = S.DA.lM := by
    show cf.lgk + 2 * cf.lt - 1 = S.lg + (S.lt - 1 - S.lB) + (S.lt - 1 - S.lB + 1) + S.lB + S.lB
    rw [C.lgk, C.lt]
    omega
  have eD : Attention.nDOf cf = S.DA.lD := by
    show cf.lgk + cf.lt + cf.lB = S.lg + (S.lt - 1 - S.lB + 1) + S.lB + S.lB
    rw [C.lgk, C.lt, C.lB]
    omega
  have es : 5 * 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) *
      (2 ^ Attention.nMOf cf + 2 ^ Attention.nDOf cf) = SM S.DA + SD S.DA := by
    rw [eM, eD, C.ll, C.H, C.lgk, ← f.nkv]
    show _ = 2 ^ S.DA.lM * (2 ^ S.ll * (S.P.nq / S.P.nkv) * 5) +
      2 ^ S.DA.lD * (2 ^ S.ll * (S.P.nq / S.P.nkv) * 5)
    ring
  rw [es, C.NAs, C.lmS]

/-- What "Attention.fill" returns has the numbers at the parameter file's lines, if the layout y
meets "Laid2", holds the shape made of that file, and its ldh is the least l with dh ≤ 2^l. -/
theorem fitsCf_of_fill {P : Model.PolScan} {y : Model.Layer.Lay} {s : Model.Layer.Scales}
    {lines : List Attention.Line} {g : ℕ} {cf : Attention.Cfg}
    (hf : Attention.fill P y s lines g = .ok cf) (L : Laid2 y)
    (hy : y.h = Model.Verify.layerShape P) (hl : y.ldh = ceilLog2 P.h.dh) (u0 : ℕ)
    (kT NC : Seg → ℕ) : FitsCf (Sz.ofHdr P.h u0 kT NC) cf := by
  have hT : y.T = 2 ^ P.h.lt := by rw [L.T, hy]; rfl
  have hq : y.mrow.getD 3 0 = 2 ^ P.h.lmq := by rw [L.mrow3, hy]; rfl
  unfold Attention.fill at hf
  obtain ⟨-, hf⟩ := L5.refuse_ok hf
  obtain ⟨-, hf⟩ := L5.refuse_ok hf
  obtain rfl := Except.ok.inj hf
  exact ⟨rfl, rfl, rfl, hl, rfl, rfl, rfl, rfl, by show 2 ^ P.h.lmh / y.T = _; rw [hT]; rfl,
    by show 2 ^ P.h.lmo / y.T = _; rw [hT]; rfl,
    by show y.mrow.getD 3 0 / y.T = _; rw [hT, hq]; rfl⟩

open OnBytes.Model.Layer (layout layoutBase) in
/-- In a layout that "Layer.layout" returns, ldh is the least l with dh ≤ 2^l. -/
theorem ldh_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hl : layout h pc = .ok y) : y.ldh = ceilLog2 h.dh := by
  unfold layout at hl
  obtain ⟨y0, hy, h1⟩ := ok_of_bind hl
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  clear hl h1
  show y0.ldh = _
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  rfl

/-- **Attention, at what the Lean verifier's functions return.** If "Layer.layout" returns y at the
shape made of a parameter file and "Attention.group" returns the plan X for group g, the numbers at
that file's lines meet "Sz.OK" and "Sz.Fit", and g is below nGr: for a valid name of attention, own
or borrowed, the number in the attention segment's list, the row and the column of its place are
"L5.addrA" at X's shape. -/
theorem place_eq_addrA_of_group {P : Model.PolScan} {pc : List (List String)}
    {y : Model.Layer.Lay} {sc : Model.Layer.Scales} {midQ : ℕ → ℕ} {lines : List Attention.Line}
    {g : ℕ} {X : Attention.Plan}
    (hy : Model.Layer.layout (Model.Verify.layerShape P) pc = .ok y)
    (hG : Attention.group P y sc midQ lines g = .ok X) {u0 : ℕ} {kT NC : Seg → ℕ}
    (h : (Sz.ofHdr P.h u0 kT NC).OK) (f : (Sz.ofHdr P.h u0 kT NC).Fit)
    (hg : g < (Sz.ofHdr P.h u0 kT NC).nGr) (c : AttSeg.Raw)
    (hv : c.Valid (Sz.ofHdr P.h u0 kT NC).DA) :
    (Sz.ofHdr P.h u0 kT NC).mu (.att g) ((Name.att g c).place (Sz.ofHdr P.h u0 kT NC)).2.1 =
        some (L5.addrA X.S c).1 ∧
      ((Name.att g c).place (Sz.ofHdr P.h u0 kT NC)).2.2.1 = (L5.addrA X.S c).2.1 ∧
      ((Name.att g c).place (Sz.ofHdr P.h u0 kT NC)).2.2.2 = (L5.addrA X.S c).2.2 := by
  obtain ⟨cf, hf, hS, -, -⟩ := L5.shaped_of_group hG
  rw [L5.addrA_lib_group hG c]
  exact place_eq_addrL h f
    (fitsA_of_shaped h f
      (fitsCf_of_fill hf (laid2_of_layout hy) (layout_shape hy) (ldh_of_layout hy) u0 kT NC) hS)
    hg c hv

/-- **The layers, at what the Lean verifier's function returns.** If "Layer.layout" returns y at the
shape made of a parameter file, that shape has the digit forms and switches of "Switches" and
profile 4, and the numbers at the file's lines meet "Sz.OK": in a group below nGr, the number in the
list, the row and the column of a valid feed-forward name's place are "placeOf" at y. -/
theorem place_eq_placeOf_of_layout {P : Model.PolScan} {pc : List (List String)}
    {y : Model.Layer.Lay} (hy : Model.Layer.layout (Model.Verify.layerShape P) pc = .ok y)
    (Sw : Switches (Model.Verify.layerShape P)) (hp4 : (Model.Verify.layerShape P).p4 = true)
    {u0 : ℕ} {kT NC : Seg → ℕ} (h : (Sz.ofHdr P.h u0 kT NC).OK) {g : ℕ}
    (hg : g < (Sz.ofHdr P.h u0 kT NC).nGr) (q : FFSeg.Cell)
    (hv : q.Valid (Sz.ofHdr P.h u0 kT NC).DF) :
    (Sz.ofHdr P.h u0 kT NC).mu (.ff g) ((Name.ff g q).place (Sz.ofHdr P.h u0 kT NC)).2.1 =
        some (placeOf y (Sz.ofHdr P.h u0 kT NC).DF q).1 ∧
      ((Name.ff g q).place (Sz.ofHdr P.h u0 kT NC)).2.2.1 =
        (placeOf y (Sz.ofHdr P.h u0 kT NC).DF q).2.1 ∧
      ((Name.ff g q).place (Sz.ofHdr P.h u0 kT NC)).2.2.2 =
        (placeOf y (Sz.ofHdr P.h u0 kT NC).DF q).2.2 := by
  have e := layout_shape hy
  exact place_eq_placeOf h (laid2_of_layout hy) (e ▸ Sw) (e ▸ fitsL_ofHdr P u0 kT NC)
    (e ▸ hp4) hg q hv

end Attention

/-! ## The head -/

/-- "FitsH" (Johnson/HonestTrace/PlacesTiesHead.lean) holds of the numbers at a parameter file's
lines and the head's shape that the Lean verifier makes of that file and any layout y ("headShape").
By definition. -/
theorem fitsH_ofHdr (P : Model.PolScan) (y : Model.Layer.Lay) (u0 : ℕ) (kT NC : Seg → ℕ) :
    FitsH (Sz.ofHdr P.h u0 kT NC) (Model.Verify.headShape P y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.planeCols_ok
#print axioms OnBytes.HonestTrace.atBit_cellRC
#print axioms OnBytes.HonestTrace.kP_of_planeCols
#print axioms OnBytes.HonestTrace.k_b_of_layout
#print axioms OnBytes.HonestTrace.k_bA_of_shapeHid
#print axioms OnBytes.HonestTrace.k_bH_of_layout
#print axioms OnBytes.HonestTrace.fitsL_ofHdr
#print axioms OnBytes.HonestTrace.T_of_fitsL
#print axioms OnBytes.HonestTrace.fcM_of_fitsL
#print axioms OnBytes.HonestTrace.roundUp_div'
#print axioms OnBytes.HonestTrace.colsM_of_fitsL
#print axioms OnBytes.HonestTrace.mu_firstM
#print axioms OnBytes.HonestTrace.place_eq_placeOf
#print axioms OnBytes.HonestTrace.adr_u0
#print axioms OnBytes.HonestTrace.phi_u0
#print axioms OnBytes.HonestTrace.tie_feat
#print axioms OnBytes.HonestTrace.addrL_of_mat
#print axioms OnBytes.HonestTrace.place_att_any
#print axioms OnBytes.HonestTrace.place_eq_addrL
#print axioms OnBytes.HonestTrace.place_eq_addrA
#print axioms OnBytes.HonestTrace.fitsA_of_shaped
#print axioms OnBytes.HonestTrace.fitsCf_of_fill
#print axioms OnBytes.HonestTrace.ldh_of_layout
#print axioms OnBytes.HonestTrace.place_eq_addrA_of_group
#print axioms OnBytes.HonestTrace.place_eq_placeOf_of_layout
#print axioms OnBytes.HonestTrace.fitsH_ofHdr
