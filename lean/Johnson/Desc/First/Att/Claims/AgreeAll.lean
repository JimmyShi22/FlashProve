-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/AgreeAll.lean: kind K5: "the tables are true", typed: Cb.Sub.Agree
(attA L u) (P.msg m) (uAt …), the premise hA of port_pull
(Johnson/Desc/First/Att/Claims/PortAll.lean), from AttAt and four named records.

Main names:
  `RowW`, `LongW`, `ColW`: the verifier's weights under a table read as the library's, by the kind
    of the table. `WeightsAre`: that for the 21 tables (paid in
    Johnson/Desc/First/Att/Claims/WeightsOf.lean).
  `PlacesIn`: every listed name's place lies in its table (paid in
    Johnson/Desc/First/Att/Claims/PlacesIn.lean).
  `CellsTie`: under every listed name, the early entry of each cell is the matrices' entry at the
    cell's address. Not shown in this file or in what it imports.
  `ScoreTabs`, `score_tabs`: the two units' six tables, out of TabsAt
    (Johnson/Desc/First/Att/Claims/TablesAt.lean).
  `agree_all`: all 21 tables at every listed name. `form_eq`. `agree_of_attAt`: Agree, at parameters
    with SizesAre, a record of names whose every late entry's name is listed (namesOf,
    Cb/Pv/Att/End/Names.lean), AttAt, TabsAt, ScoreTabs, WeightsAre, PlacesIn and CellsTie.
Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem on such a
routine's return; the runs spoken of are the kind's own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58
import Johnson.Desc.First.Att.Claims.AgreeKind
import Johnson.Desc.First.Att.Claims.TablesAt
import Johnson.Desc.First.Att.Claims.PortAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (AttTab TabW namesOf LateLay)

variable {Kf : Type} [Field Kf]

/-- The verifier's weights on the positions read as the library's. -/
def RowW (ρ : Reading Kf) (h : Attention.Heard) (phi : Array E) (w : TabW Kf) : Prop :=
  ∃ Ψ, w = .row Ψ ∧ ∀ i < h.S.T, ρ.val (phi.getD i zeroE) = Ψ i

/-- The verifier's weights on the features of a block (from the point zc) and on the positions read as the library's. -/
def LongW (ρ : Reading Kf) (h : Attention.Heard) (zc tokv : Array E) (w : TabW Kf) : Prop :=
  ∃ lw Ψ, w = .long lw Ψ ∧ (lowOf h.S zc).size = 2 ^ h.S.ls ∧ tokv.size = h.S.T ∧
    (∀ c < 2 ^ h.S.ls, ρ.val ((lowOf h.S zc).getD c zeroE) = lw c) ∧
    ∀ i < h.S.T, ρ.val (tokv.getD i zeroE) = Ψ i

/-- The verifier's weights on the cells of an entry of as read as the library's. -/
def ColW (ρ : Reading Kf) (h : Attention.Heard) (phi : Array E) (w : TabW Kf) : Prop :=
  ∃ ph, w = .col ph ∧ ∀ k < 2 ^ h.S.cf.lmS, ρ.val (phi.getD k zeroE) = ph k

/-- **The weights of the 21 tables**: what the verifier lays under each table (tabs_at) reads as the weights tb that the library means. kM, kD: the two units; zx: the lookup's point inside a tree. -/
structure WeightsAre (ρ : Reading Kf) (h : Attention.Heard) (kM kD : Score) (zx : Array E)
    (tb : AttTab → TabW Kf) : Prop where
  tMm : RowW ρ h (tok h.S kM.wI kM.zi) (tb .tMm)
  tMd : RowW ρ h (tok h.S kD.wI kD.zi) (tb .tMd)
  hW : RowW ρ h (eqTab h.d.ziW) (tb .hW)
  hX : RowW ρ h (eqTab h.d.ziX) (tb .hX)
  hE : RowW ρ h (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))) (tb .hE)
  hT : RowW ρ h (eqTab h.x.ti) (tb .hT)
  hPi : RowW ρ h (eqTab (h.x.pi h.S)) (tb .hPi)
  hR2 : RowW ρ h (eqTab (h.x.ri2 h.S)) (tb .hR2)
  tQm : LongW ρ h (lastCoords kM.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kM).1 kM.zi) (tb .tQm)
  tKm : LongW ρ h (lastCoords kM.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kM).2 kM.zj) (tb .tKm)
  tQd : LongW ρ h (lastCoords kD.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kD).1 kD.zi) (tb .tQd)
  tKd : LongW ρ h (lastCoords kD.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kD).2 kD.zj) (tb .tKd)
  qO : LongW ρ h (h.d.zcW) (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))) (tb .qO)
  qVM : LongW ρ h (h.d.zcW) (tok h.S h.d.wJv (lastCoords h.d.vpm.r h.S.cf.lB)) (tb .qVM)
  qVD : LongW ρ h (h.d.zcW) (tok h.S (eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT))) (lastCoords h.d.vpd.r h.S.cf.lB)) (tb .qVD)
  qF : LongW ρ h (h.x.rc h.S) (eqTab (h.x.ri h.S)) (tb .qF)
  qKx : LongW ρ h (h.x.rc h.S) (eqTab (h.x.pj h.S)) (tb .qKx)
  tO : LongW ρ h (h.d.zcW) (eqTab h.d.ziW) (tb .tO)
  tA : ColW ρ h (lastN zx h.S.cf.lmS) (tb .tA)
  tVM : ColW ρ h (lastN h.t.ptM h.S.cf.lmS) (tb .tVM)
  tVD : ColW ρ h (lastN h.t.ptD h.S.cf.lmS) (tb .tVD)

/-- Every listed name's place lies in its table. -/
def PlacesIn (h : Attention.Heard) : Prop :=
  ∀ T, ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T,
    placeAtt h.S T r < (h.t.tabLen.lookup (tabOfAtt h T)).getD 0

/-- **The cells' tie**: under every listed name, the early entry of each cell is the matrices' entry at the cell's address. -/
structure CellsTie {J₁ : Type} (h : Attention.Heard) (M : Mats Kf) (cellJ : Raw → J₁) (x : J₁ → Kf) : Prop where
  row : ∀ T ∈ rowTabs, ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T, ∀ k < h.S.T,
    x (cellJ (r.atPos k)) = cellsK h.S M (r.atPos k)
  long : ∀ T, T ∈ qaTabs ∨ T = .tO → ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T,
    ∀ c < 2 ^ h.S.ls, ∀ i < h.S.T, x (cellJ ((r.addN c).atPos i)) = cellsK h.S M ((r.addN c).atPos i)
  col : ∀ T ∈ colTabs, ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T, ∀ k < 2 ^ h.S.cf.lmS,
    x (cellJ (r.addX k)) = cellsK h.S M (r.addX k)

/-- The two units' six tables, as the list of tables has them. -/
structure ScoreTabs (tl : HTailF2) (h : Attention.Heard) (kM kD : Score) : Prop where
  mM : AhAt tl h (h.t.score.getD 0 default).tM (tok h.S kM.wI kM.zi)
  mQ : QaAt tl h (h.t.score.getD 0 default).tQ (lastCoords kM.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kM).1 kM.zi)
  mK : QaAt tl h (h.t.score.getD 0 default).tK (lastCoords kM.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kM).2 kM.zj)
  dM : AhAt tl h (h.t.score.getD 1 default).tM (tok h.S kD.wI kD.zi)
  dQ : QaAt tl h (h.t.score.getD 1 default).tQ (lastCoords kD.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kD).1 kD.zi)
  dK : QaAt tl h (h.t.score.getD 1 default).tK (lastCoords kD.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kD).2 kD.zj)

theorem score_tabs {tl : HTailF2} {h : Attention.Heard} {zx : Array E} {kM kD : Score} (Tb : TabsAt tl h zx)
    (hs : h.scores.toList = [kM, kD]) : ScoreTabs tl h kM kD := by
  have F := Tb.score
  rw [hs] at F
  obtain ⟨t0, l1, a0, F1, e0⟩ := List.forall₂_cons_left_iff.1 F
  obtain ⟨t1, l2, a1, F2, e1⟩ := List.forall₂_cons_left_iff.1 F1
  have e2 := List.forall₂_nil_left_iff.1 F2
  subst e2 e1
  have g0 : h.t.score.getD 0 default = t0 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e0]; rfl
  have g1 : h.t.score.getD 1 default = t1 := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e0]; rfl
  rw [← g0] at a0
  rw [← g1] at a1
  exact ⟨a0.1, a0.2.1, a0.2.2, a1.1, a1.2.1, a1.2.2⟩

variable {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {cellJ : Raw → J₁} {x : J₁ → Kf}

/-- **Every table, at every listed name**: the vector's entry at the name's place is what the library means the late entry of that name to be. -/
theorem agree_all (A : AttAt ρ W tl K3 M h lid cf fs) {zx : Array E} (Tb : TabsAt tl h zx) {kM kD : Score}
    (Sc : ScoreTabs tl h kM kD) {tb : AttTab → TabW Kf} (Wt : WeightsAre ρ h kM kD zx tb)
    (Pl : PlacesIn h) (Ct : CellsTie h M cellJ x) (T : AttTab) (r : Raw)
    (hr : r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T) :
    rdW W h.iU3 K3 (tabOfAtt h T + placeAtt h.S T r) =
      ((tb T).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have row : ∀ {T : AttTab} {phi : Array E}, T ∈ rowTabs → TabAt tl h (tabOfAtt h T) h.S.cf.NAs h.S.T phi →
      RowW ρ h phi (tb T) → ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T,
      rdW W h.iU3 K3 (tabOfAtt h T + placeAtt h.S T r) =
        ((tb T).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
    intro T phi hT Ta ⟨Ψ, e, w⟩ r hr
    rw [e]
    exact agree_row A hT Ta w hr (Pl T r hr) (Ct.row T hT r hr)
  have qa : ∀ {T : AttTab} {zc tokv : Array E}, T ∈ qaTabs → QaAt tl h (tabOfAtt h T) zc tokv →
      LongW ρ h zc tokv (tb T) → ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T,
      rdW W h.iU3 K3 (tabOfAtt h T + placeAtt h.S T r) =
        ((tb T).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
    intro T zc tokv hT Ta ⟨lw, Ψ, e, s1, s2, w1, w2⟩ r hr
    rw [e]
    exact agree_long A Ta (by rw [A.mats.nm]; omega) A.mats.qaM Z.wcQ s1 s2 w1 w2 (Pl T r hr)
      (fun k hk => names_qa h.S N Z hT hr hk) (Ct.long T (.inl hT) r hr)
  have col : ∀ {T : AttTab} {phi : Array E}, T ∈ colTabs → AsAt h (tabOfAtt h T) phi →
      ColW ρ h phi (tb T) → ∀ r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T,
      rdW W h.iU3 K3 (tabOfAtt h T + placeAtt h.S T r) =
        ((tb T).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
    intro T phi hT Ta ⟨ph, e, w⟩ r hr
    rw [e]
    exact agree_col A hT Ta w hr (Pl T r hr) (Ct.col T hT r hr)
  cases T with
  | tMm => exact row (T := .tMm) (by simp [rowTabs]) Sc.mM Wt.tMm r hr
  | tMd => exact row (T := .tMd) (by simp [rowTabs]) Sc.dM Wt.tMd r hr
  | hW => exact row (T := .hW) (by simp [rowTabs]) Tb.hW Wt.hW r hr
  | hX => exact row (T := .hX) (by simp [rowTabs]) Tb.hX Wt.hX r hr
  | hE => exact row (T := .hE) (by simp [rowTabs]) Tb.hE Wt.hE r hr
  | hT => exact row (T := .hT) (by simp [rowTabs]) Tb.hT Wt.hT r hr
  | hPi => exact row (T := .hPi) (by simp [rowTabs]) Tb.hPi Wt.hPi r hr
  | hR2 => exact row (T := .hR2) (by simp [rowTabs]) Tb.hR2 Wt.hR2 r hr
  | tQm => exact qa (T := .tQm) (by simp [qaTabs]) Sc.mQ Wt.tQm r hr
  | tKm => exact qa (T := .tKm) (by simp [qaTabs]) Sc.mK Wt.tKm r hr
  | tQd => exact qa (T := .tQd) (by simp [qaTabs]) Sc.dQ Wt.tQd r hr
  | tKd => exact qa (T := .tKd) (by simp [qaTabs]) Sc.dK Wt.tKd r hr
  | qO => exact qa (T := .qO) (by simp [qaTabs]) Tb.qO Wt.qO r hr
  | qVM => exact qa (T := .qVM) (by simp [qaTabs]) Tb.qVM Wt.qVM r hr
  | qVD => exact qa (T := .qVD) (by simp [qaTabs]) Tb.qVD Wt.qVD r hr
  | qF => exact qa (T := .qF) (by simp [qaTabs]) Tb.qF Wt.qF r hr
  | qKx => exact qa (T := .qKx) (by simp [qaTabs]) Tb.qKx Wt.qKx r hr
  | tA => exact col (T := .tA) (by simp [colTabs]) Tb.tA Wt.tA r hr
  | tVM => exact col (T := .tVM) (by simp [colTabs]) Tb.tVM Wt.tVM r hr
  | tVD => exact col (T := .tVD) (by simp [colTabs]) Tb.tVD Wt.tVD r hr
  | tO =>
    obtain ⟨lw, Ψ, e, s1, s2, w1, w2⟩ := Wt.tO
    rw [e]
    exact agree_long A Tb.tO (by rw [A.mats.nm]; omega) A.mats.aoM Z.wcO s1 s2 w1 w2 (Pl .tO r hr)
      (fun k hk => names_tO h.S N Z hr hk) (Ct.long .tO (.inr rfl) r hr)

omit [Fintype J₁] in
theorem form_eq (w : TabW Kf) {D D' : Inst.Model.AttSeg.Dim} {ls ls' lmS lmS' : ℕ} (hD : D = D') (h1 : ls = ls')
    (h2 : lmS = lmS') (r : Raw) : w.form cellJ D ls lmS r = w.form cellJ D' ls' lmS' r := by
  subst hD h1 h2
  rfl

open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (EndLay attA attTb lateA)

/-- **"The tables are true", typed**: where every table of the list is true of the matrices M in W (AttAt), the tables lie in the list as TabsAt says, their weights read as the library's (WeightsAre), every listed name's place lies in its table (PlacesIn) and the cells of P.msg m are M's (CellsTie): each late entry read off the world is worth its meant form. -/
theorem agree_of_attAt [Fintype Kf] {Mg X : Type} {J₂ : Type} [Fintype J₂] [DecidableEq J₂]
    {P : OwnPar Kf Mg X} {L : EndLay P J₂} {u : P.Run} {m : Mg} (Z : SizesAre P L h)
    (A : AttAt ρ W tl K3 M h lid cf fs) {zx : Array E} (Tb : TabsAt tl h zx) {kM kD : Score}
    (Sc : ScoreTabs tl h kM kD) (Wt : WeightsAre ρ h kM kD zx (attTb L u)) (Pl : PlacesIn h)
    (Ct : CellsTie h M L.cellJ (P.msg m))
    (hY : ∀ j, (L.Y.nm j).2 ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS (L.Y.nm j).1) :
    Cb.Sub.Agree (attA L u) (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)) := by
  intro j
  show rdW W h.iU3 K3 (tabOfAtt h (L.Y.nm j).1 + placeAtt h.S (L.Y.nm j).1 (L.Y.nm j).2) =
    ((attTb L u (L.Y.nm j).1).form L.cellJ P.D L.ls L.lmS (L.Y.nm j).2).val (P.msg m)
  rw [form_eq _ Z.D Z.ls Z.lmS]
  exact agree_all A Tb Sc Wt Pl Ct _ _ (hY j)

end K5Law
