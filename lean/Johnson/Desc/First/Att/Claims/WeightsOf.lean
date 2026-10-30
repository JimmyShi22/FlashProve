-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WeightsOf.lean: kind K5: the record WeightsAre
(Johnson/Desc/First/Att/Claims/AgreeAll.lean), paid: what the verifier lays under each of the 21
tables reads as the weights that the library means (attTb, Cb/Pv/Att/End/Cl.lean).

Main names:
  `Xi`: the library-side letters that the weights read. `tbAt D C ls lmS X`: attTb's text at these
    letters. `xiOf u`: the letters at a run. `attTb_eq`: attTb L u = tbAt P.D P.C L.ls L.lmS (xiOf
    u), by definition.
  `XiIs ρ h kM kD zx C X`: what the verifier's points and weights read as, in the letters X.
  `cutv`, `lastv`, `cat_sh`, `colW_gen`; `w_rows` (8 tables), `w_cols` (3), `w_long_eq` (5),
    `w_long_tile` (5); `weights_at`: WeightsAre at tbAt (dimOf h.S) C h.S.ls h.S.cf.lmS X, from
    XiIs.
By Johnson/Desc/First/Att/Claims/WeightsKit.lean and tiles_row, tiles_col, scoreTiles_fm,
scoreTiles_fd (Johnson/Road/Rows/AttEnds14Tiles.lean).
Limit: XiIs is a premise here; Johnson/Desc/First/Att/Claims/AgreeTop.lean pays a part of it.

Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.End.Cl
import Johnson.Desc.First.Att.Claims.WeightsKit

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Cb.Pv.Att
open Blocks (eqN)
open Inst.Model.AttSeg (Dim Calls Pub eqT cat sh inn zP zs zi' zj' zID yi xi yn psiRow psiCol blkRow blkCol)
open Cb.Pv.Att.End (AttTab TabW EndLay attTb ptN ptOn zT)

variable {Kf : Type} [Field Kf]

/-- The library-side letters that the weights of the 21 tables read: the lookup's end point z; the z of five output statements' states; the eight sumchecks' points; the drawn point's part ti; the score's point's part fn; two states. -/
structure Xi (Kf : Type) where
  z : ℕ → Kf
  zM : ℕ → Kf
  zD : ℕ → Kf
  zE : ℕ → Kf
  zVM : ℕ → Kf
  zVD : ℕ → Kf
  xM : ℕ → Kf
  xD : ℕ → Kf
  xE : ℕ → Kf
  xVM : ℕ → Kf
  xVD : ℕ → Kf
  xF : ℕ → Kf
  xK : ℕ → Kf
  xH : ℕ → Kf
  ti : ℕ → Kf
  fn : ℕ → Kf
  stVM : Pub Kf
  stVD : Pub Kf

/-- The weights of the tables (Cb/Pv/Att/End/Cl.lean: attTb), at these letters. -/
noncomputable def tbAt (D : Dim) (C : Calls) (ls lmS : ℕ) (X : Xi Kf) : AttTab → TabW Kf
  | .tA => .col (eqN lmS (D.lM - lmS) (inn D C X.z .m1))
  | .tMm => .row (psiRow D (zP D C X.z) (zs D C X.z) (zi' D C X.z))
  | .tMd => .row (eqT D (cat (D.lP + 1) (zID D C X.z) (zi' D C X.z)))
  | .hW => .row (eqT D (yi D C X.z))
  | .hX => .row (eqT D (xi D C X.z))
  | .tO => .long (eqN ls (D.ln - ls) (yn D C X.z)) (eqT D (yi D C X.z))
  | .tQm => .long (eqN ls (D.ln - ls) (sh X.xM (D.lg + D.lP + (D.lP + 1))))
      (psiRow D (sh X.xM D.lg) (sh X.xM (D.lg + D.lP)) (zi' D C X.zM))
  | .tKm => .long (eqN ls (D.ln - ls) (sh X.xM (D.lg + D.lP + (D.lP + 1))))
      (psiCol D (sh X.xM D.lg) (sh X.xM (D.lg + D.lP)) (zj' D C X.zM))
  | .tQd => .long (eqN ls (D.ln - ls) (sh X.xD (D.lg + (D.lP + 1)))) (psiDiag D (sh X.xD D.lg) (zi' D C X.zD))
  | .tKd => .long (eqN ls (D.ln - ls) (sh X.xD (D.lg + (D.lP + 1)))) (psiDiag D (sh X.xD D.lg) (zj' D C X.zD))
  | .hE => .row (eqT D (sh X.xE D.lg))
  | .qO => .long (eqN ls (D.ln - ls) (yn D C X.zE)) (eqT D (sh X.xE D.lg))
  | .tVM => .col (eqN lmS (D.lM - lmS) (ptBelow D C X.stVM X.xVM))
  | .qVM => .long (eqN ls (D.ln - ls) (yn D C X.zVM))
      (psiCol D (sh X.xVM D.lg) (sh X.xVM (D.lg + D.lP)) (sh X.xVM (D.lg + D.lP + (D.lP + 1))))
  | .tVD => .col (eqN lmS (D.lD - lmS) (ptOn D C X.stVD X.xVD))
  | .qVD => .long (eqN ls (D.ln - ls) (yn D C X.zVD)) (eqT D (sh X.xVD D.lg))
  | .hT => .row (eqT D X.ti)
  | .qF => .long (eqN ls (D.ln - ls) (sh X.xF (D.lT + D.lg))) (eqT D X.xF)
  | .qKx => .long (eqN ls (D.ln - ls) X.fn) (eqT D X.xK)
  | .hPi => .row (eqT D (sh X.xK (D.lT + D.lg)))
  | .hR2 => .row (eqT D X.xH)

/-- The letters at a run. -/
noncomputable def xiOf [Fintype Kf] {M X : Type} {P : OwnPar Kf M X} (u : P.Run) : Xi Kf :=
  ⟨zT u, Pub.z u.oM.st, Pub.z u.oD.st, Pub.z u.oE.st, Pub.z u.oVM.st, Pub.z u.oVD.st,
    ptN P.uM.T u.oM, ptN P.uD.T u.oD, ptN P.sE.T u.oE, ptN P.sVM.T u.oVM, ptN P.sVD.T u.oVD,
    ptN P.sF.T u.oF, ptN P.sD.T u.oK, ptN P.sH.T u.oH, (P.pubZ u.z).ti, Pub.fn (Prod.fst u.oK.st),
    u.oVM.st, u.oVD.st⟩

theorem attTb_eq [Fintype Kf] {M X J₂ : Type} {P : OwnPar Kf M X} (L : EndLay P J₂) (u : P.Run) :
    attTb L u = tbAt P.D P.C L.ls L.lmS (xiOf u) := by
  funext T
  cases T <;> rfl

/-- A stretch of the challenges of a sumcheck, against the library's point. -/
theorem cutv {ρ : Reading Kf} {r : Array E} {ξ : ℕ → Kf} (p : ∀ j, ξ j = pt ρ r j) {a b : ℕ} (hb : b ≤ r.size) :
    (r.extract a b).size = b - a ∧ ∀ j < b - a, pt ρ (r.extract a b) j = sh ξ a j :=
  ⟨sizeCut r hb, fun j hj => by
    rw [ptCut ρ r hb (by omega)]
    exact (p _).symm⟩

/-- **What the verifier's points and weights read as**, in the letters X. kM, kD: the two units; zx: the lookup's point inside a tree. -/
structure XiIs (ρ : Reading Kf) (h : Attention.Heard) (kM kD : Score) (zx : Array E) (C : Calls) (X : Xi Kf) :
    Prop where
  nums : WNums h
  zM : X.zM = X.z
  zD : X.zD = X.z
  zE : X.zE = X.z
  zVM : X.zVM = X.z
  zVD : X.zVD = X.z
  wIM : ∀ I < h.S.nT, ρ.val (kM.wI.getD I zeroE) =
    blkRow (L5.dimOf h.S) (zP (L5.dimOf h.S) C X.z) (zs (L5.dimOf h.S) C X.z) I
  siM : kM.zi.size = h.S.cf.lB
  iM : ∀ j < h.S.cf.lB, pt ρ kM.zi j = zi' (L5.dimOf h.S) C X.z j
  sjM : kM.zj.size = h.S.cf.lB
  jM : ∀ j < h.S.cf.lB, pt ρ kM.zj j = zj' (L5.dimOf h.S) C X.z j
  wID : ∀ I < h.S.nT, ρ.val (kD.wI.getD I zeroE) = eqN ((L5.dimOf h.S).lP + 1) 0 (zID (L5.dimOf h.S) C X.z) I
  siD : kD.zi.size = h.S.cf.lB
  iD : ∀ j < h.S.cf.lB, pt ρ kD.zi j = zi' (L5.dimOf h.S) C X.z j
  sjD : kD.zj.size = h.S.cf.lB
  jD : ∀ j < h.S.cf.lB, pt ρ kD.zj j = zj' (L5.dimOf h.S) C X.z j
  siW : h.d.ziW.size = h.S.cf.lt
  iW : ∀ j < h.S.cf.lt, pt ρ h.d.ziW j = yi (L5.dimOf h.S) C X.z j
  siX : h.d.ziX.size = h.S.cf.lt
  iX : ∀ j < h.S.cf.lt, pt ρ h.d.ziX j = xi (L5.dimOf h.S) C X.z j
  scW : h.d.zcW.size = h.S.cf.ldh
  nW : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) C X.z j
  sA : h.S.cf.lmS ≤ zx.size
  vA : ∀ j < h.S.cf.lmS, pt ρ zx (zx.size - h.S.cf.lmS + j) =
    inn (L5.dimOf h.S) C X.z .m1 ((L5.dimOf h.S).lM - h.S.cf.lmS + j)
  segM : kM.seg = .fm
  segD : kD.seg = .fd
  rM : kM.sc.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.ldh
  pM : ∀ j, X.xM j = pt ρ kM.sc.r j
  rD : kD.sc.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.ldh
  pD : ∀ j, X.xD j = pt ρ kD.sc.r j
  rE : h.d.scE.r.size = h.S.cf.lgk + h.S.cf.lt
  pE : ∀ j, X.xE j = pt ρ h.d.scE.r j
  rVM : h.d.vpm.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB
  pVM : ∀ j, X.xVM j = pt ρ h.d.vpm.r j
  rVD : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB
  pVD : ∀ j, X.xVD j = pt ρ h.d.vpd.r j
  rF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh
  pF : ∀ j, X.xF j = pt ρ h.x.scF.r j
  rK : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk
  pK : ∀ j, X.xK j = pt ρ h.x.scd.r j
  rH : h.S.cf.lt ≤ h.x.scH.r.size
  pH : ∀ j, X.xH j = pt ρ h.x.scH.r j
  wJv : h.d.wJv = (tileSums h.S
    (eqTab (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))))
    (eqTab (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1)) (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)))).2
  sti : h.x.ti.size = h.S.cf.lt
  ti : ∀ j < h.S.cf.lt, pt ρ h.x.ti j = X.ti j
  fn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = X.fn j
  nM : (L5.dimOf h.S).lM = h.S.nM
  nD : (L5.dimOf h.S).lD = h.S.nD
  lmM : h.S.cf.lmS ≤ h.S.nM
  sPM : h.t.ptM.size = h.S.nM
  ptM : ∀ j < h.S.nM, pt ρ h.t.ptM j = ptBelow (L5.dimOf h.S) C X.stVM X.xVM j
  sPD : h.t.ptD.size = h.S.nD
  ptD : ∀ j < h.S.nD, pt ρ h.t.ptD j = ptOn (L5.dimOf h.S) C X.stVD X.xVD j

variable {ρ : Reading Kf} {h : Attention.Heard} {kM kD : Score} {zx : Array E} {C : Calls} {X : Xi Kf}

local notation "TB" => tbAt (L5.dimOf h.S) C h.S.ls h.S.cf.lmS X

/-- The eight tables on ah. -/
theorem w_rows (I : XiIs ρ h kM kD zx C X) :
    RowW ρ h (tok h.S kM.wI kM.zi) (TB .tMm) ∧ RowW ρ h (tok h.S kD.wI kD.zi) (TB .tMd) ∧
    RowW ρ h (eqTab h.d.ziW) (TB .hW) ∧ RowW ρ h (eqTab h.d.ziX) (TB .hX) ∧
    RowW ρ h (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))) (TB .hE) ∧
    RowW ρ h (eqTab h.x.ti) (TB .hT) ∧ RowW ρ h (eqTab (h.x.pi h.S)) (TB .hPi) ∧
    RowW ρ h (eqTab (h.x.ri2 h.S)) (TB .hR2) := by
  have Nn := I.nums
  refine ⟨rowW_of (tok_tile Nn I.wIM I.siM I.iM), ?_, rowW_of (tok_eq Nn I.siW I.iW),
    rowW_of (tok_eq Nn I.siX I.iX), ?_, rowW_of (tok_eq Nn I.sti I.ti), ?_, ?_⟩
  · obtain ⟨s, w⟩ := tok_tile Nn I.wID I.siD I.iD
    exact rowW_of ⟨s, fun i hi => by rw [w i hi]; exact eqT_tile _ _ _ i⟩
  · obtain ⟨s, w⟩ := cutv I.pE (a := h.S.cf.lgk) (b := h.S.cf.lgk + h.S.cf.lt) (by rw [I.rE])
    exact rowW_of (tok_eq Nn (by rw [s]; omega) fun j hj => w j (by omega))
  · obtain ⟨s, w⟩ := cutv I.pK (a := h.S.cf.lt + h.S.cf.lgk) (b := 2 * h.S.cf.lt + h.S.cf.lgk) (by rw [I.rK])
    show RowW ρ h _ (.row (eqT (L5.dimOf h.S) (sh X.xK ((L5.dimOf h.S).lT + h.S.cf.lgk))))
    rw [Nn.lT]
    exact rowW_of (tok_eq Nn (z := h.x.pi h.S) (s.trans (by omega)) fun j hj => w j (by omega))
  · obtain ⟨s, w⟩ := cutv I.pH (a := 0) (b := h.S.cf.lt) I.rH
    exact rowW_of (tok_eq Nn (z := h.x.ri2 h.S) (s.trans (by omega)) fun j hj =>
      (w j (by omega)).trans (by show X.xH (0 + j) = _; rw [Nat.zero_add]))

/-- The weights of a table on as, from the last lmS coordinates of any point. -/
theorem colW_gen {z : Array E} {off : ℕ} {v : ℕ → Kf} (hz : h.S.cf.lmS ≤ z.size)
    (hv : ∀ j < h.S.cf.lmS, pt ρ z (z.size - h.S.cf.lmS + j) = v (off + j)) :
    ColW ρ h (lastN z h.S.cf.lmS) (.col (eqN h.S.cf.lmS off v)) := by
  refine ⟨_, rfl, fun k hk => ?_⟩
  have s1 : (lastCoords z h.S.cf.lmS).size = h.S.cf.lmS := by
    unfold lastCoords
    rw [Array.size_extract]
    omega
  unfold lastN
  rw [eqTab_value ρ _ k (by rw [s1]; exact hk), s1, ← eqN_shift' h.S.cf.lmS off]
  refine eqN_agree (fun j hj => ?_) k
  rw [Nat.zero_add]
  unfold lastCoords
  rw [ptCut ρ z (Nat.le_refl _) (by omega)]
  exact hv j hj

/-- The three tables on as. -/
theorem w_cols (I : XiIs ρ h kM kD zx C X) :
    ColW ρ h (lastN zx h.S.cf.lmS) (TB .tA) ∧ ColW ρ h (lastN h.t.ptM h.S.cf.lmS) (TB .tVM) ∧
    ColW ρ h (lastN h.t.ptD h.S.cf.lmS) (TB .tVD) := by
  have hD := I.nums.Z.lmS
  have hM := I.lmM
  refine ⟨colW_gen I.sA I.vA, colW_gen (by rw [I.sPM]; exact hM) fun j hj => ?_,
    colW_gen (by rw [I.sPD]; exact hD) fun j hj => ?_⟩
  · rw [I.sPM, I.nM]
    exact I.ptM _ (by omega)
  · rw [I.sPD, I.nD]
    exact I.ptD _ (by omega)

omit [Field Kf] in
/-- A point cut in two and laid together again. -/
theorem cat_sh (ξ : ℕ → Kf) (a n : ℕ) : cat n (sh ξ a) (sh ξ (a + n)) = sh ξ a := by
  funext t
  unfold cat sh
  split
  · rfl
  · congr 1
    omega

/-- The last n of a sumcheck's challenges. -/
theorem lastv {r : Array E} {ξ : ℕ → Kf} (p : ∀ j, ξ j = pt ρ r j) {n a : ℕ} (hs : r.size = a + n) :
    (lastCoords r n).size = n ∧ ∀ j < n, pt ρ (lastCoords r n) j = sh ξ a j := by
  obtain ⟨s, w⟩ := cutv p (a := r.size - n) (b := r.size) (Nat.le_refl _)
  have e : r.size - n = a := by omega
  exact ⟨s.trans (by omega), fun j hj => (w j (by omega)).trans (by rw [e])⟩

/-- Five of the ten tables on blocks of features: those whose weights on the positions are equality weights. -/
theorem w_long_eq (I : XiIs ρ h kM kD zx C X) :
    LongW ρ h h.d.zcW (eqTab h.d.ziW) (TB .tO) ∧
    LongW ρ h h.d.zcW (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))) (TB .qO) ∧
    LongW ρ h (h.x.rc h.S) (eqTab (h.x.ri h.S)) (TB .qF) ∧
    LongW ρ h (h.x.rc h.S) (eqTab (h.x.pj h.S)) (TB .qKx) ∧
    LongW ρ h h.d.zcW
      (tok h.S (eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT))) (lastCoords h.d.vpd.r h.S.cf.lB))
      (TB .qVD) := by
  have Nn := I.nums
  have hl := Nn.Z.lnT
  obtain ⟨sE, wE⟩ := cutv I.pE (a := h.S.cf.lgk) (b := h.S.cf.lgk + h.S.cf.lt) (by rw [I.rE])
  obtain ⟨sc, wc⟩ := cutv I.pF (a := h.S.cf.lt + h.S.cf.lgk) (b := h.x.scF.r.size) (Nat.le_refl _)
  obtain ⟨si, wi⟩ := cutv I.pF (a := 0) (b := h.S.cf.lt) (by rw [I.rF]; omega)
  obtain ⟨sj, wj⟩ := cutv I.pK (a := 0) (b := h.S.cf.lt) (by rw [I.rK]; omega)
  have src : (h.x.rc h.S).size = h.S.cf.ldh := sc.trans (by rw [I.rF]; omega)
  refine ⟨longW_of Nn I.scW I.nW (tok_eq Nn I.siW I.iW), ?_, ?_, ?_, ?_⟩
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls) (yn (L5.dimOf h.S) C X.zE)) _)
    rw [I.zE]
    exact longW_of Nn I.scW I.nW (tok_eq Nn (sE.trans (by omega)) fun j hj => wE j (by omega))
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls) (sh X.xF ((L5.dimOf h.S).lT + h.S.cf.lgk))) _)
    rw [Nn.lT]
    exact longW_of Nn src (fun j hj => wc j (by rw [I.rF]; omega))
      (tok_eq Nn (z := h.x.ri h.S) (si.trans (by omega)) fun j hj =>
        (wi j (by omega)).trans (by show X.xF (0 + j) = _; rw [Nat.zero_add]))
  · exact longW_of Nn src I.fn (tok_eq Nn (z := h.x.pj h.S) (sj.trans (by omega)) fun j hj =>
      (wj j (by omega)).trans (by show X.xK (0 + j) = _; rw [Nat.zero_add]))
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls) (yn (L5.dimOf h.S) C X.zVD)) _)
    rw [I.zVD]
    obtain ⟨s1, w1⟩ := cutv I.pVD (a := h.S.cf.lgk) (b := h.S.cf.lgk + h.S.lnT) (by rw [I.rVD]; omega)
    obtain ⟨s2, w2⟩ := lastv I.pVD (n := h.S.cf.lB) (a := h.S.cf.lgk + h.S.lnT) I.rVD
    have eP : (L5.dimOf h.S).lP + 1 = h.S.lnT := by show h.S.lnT - 1 + 1 = _; omega
    obtain ⟨s, w⟩ := tok_tile Nn (hi := eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)))
      (w := eqN ((L5.dimOf h.S).lP + 1) 0 (sh X.xVD h.S.cf.lgk))
      (fun J hJ => by
        rw [eP]
        exact eqTab_at ρ (s1.trans (by omega)) (fun j hj => w1 j (by omega)) (by rw [← Nn.Z.nT]; exact hJ))
      s2 w2
    refine longW_of Nn I.scW I.nW ⟨s, fun i hi => ?_⟩
    rw [w i hi, eqT_tile]
    have e := cat_sh X.xVD h.S.cf.lgk ((L5.dimOf h.S).lP + 1)
    rw [eP] at e ⊢
    rw [e]
    rfl

/-- The five others: their weights on the positions go by tiles. -/
theorem w_long_tile (I : XiIs ρ h kM kD zx C X) :
    LongW ρ h (lastCoords kM.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kM).1 kM.zi) (TB .tQm) ∧
    LongW ρ h (lastCoords kM.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kM).2 kM.zj) (TB .tKm) ∧
    LongW ρ h (lastCoords kD.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kD).1 kD.zi) (TB .tQd) ∧
    LongW ρ h (lastCoords kD.sc.r h.S.cf.ldh) (tok h.S (scoreTiles h.S kD).2 kD.zj) (TB .tKd) ∧
    LongW ρ h h.d.zcW (tok h.S h.d.wJv (lastCoords h.d.vpm.r h.S.cf.lB)) (TB .qVM) := by
  have Nn := I.nums
  have Z := Nn.Z
  have hl := Z.lnT
  have e1 : h.S.cf.lgk + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1) = h.S.cf.lgk + 2 * h.S.lnT - 1 := by
    show h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1) = _
    omega
  have e2 : h.S.cf.lgk + (L5.dimOf h.S).lP = h.S.cf.lgk + h.S.lnT - 1 := by
    show h.S.cf.lgk + (h.S.lnT - 1) = _
    omega
  have e3 : h.S.cf.lgk + ((L5.dimOf h.S).lP + 1) = h.S.cf.lgk + h.S.lnT := by
    show h.S.cf.lgk + (h.S.lnT - 1 + 1) = _
    omega
  have eP : (L5.dimOf h.S).lP + 1 = h.S.lnT := by show h.S.lnT - 1 + 1 = _; omega
  -- the unit below the diagonal
  obtain ⟨sMc, wMc⟩ := lastv I.pM (n := h.S.cf.ldh) (a := h.S.cf.lgk + 2 * h.S.lnT - 1) I.rM
  obtain ⟨sMP, wMP⟩ := cutv I.pM (a := h.S.cf.lgk) (b := h.S.cf.lgk + h.S.lnT - 1) (by rw [I.rM]; omega)
  obtain ⟨sMs, wMs⟩ := cutv I.pM (a := h.S.cf.lgk + h.S.lnT - 1) (b := h.S.cf.lgk + 2 * h.S.lnT - 1)
    (by rw [I.rM]; omega)
  -- the unit on the diagonal
  obtain ⟨sDc, wDc⟩ := lastv I.pD (n := h.S.cf.ldh) (a := h.S.cf.lgk + h.S.lnT) I.rD
  obtain ⟨sDI, wDI⟩ := cutv I.pD (a := h.S.cf.lgk) (b := h.S.cf.lgk + h.S.lnT) (by rw [I.rD]; omega)
  have hDI : ∀ J < h.S.nT, ρ.val ((eqTab (kD.sc.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT))).getD J zeroE) =
      eqN ((L5.dimOf h.S).lP + 1) 0 (sh X.xD h.S.cf.lgk) J := fun J hJ => by
    rw [eP]
    exact eqTab_at ρ (sDI.trans (by omega)) (fun j hj => wDI j (by omega)) (by rw [← Z.nT]; exact hJ)
  -- the value product below the diagonal
  obtain ⟨sVl, wVl⟩ := lastv I.pVM (n := h.S.cf.lB) (a := h.S.cf.lgk + 2 * h.S.lnT - 1) I.rVM
  obtain ⟨sVP, wVP⟩ := cutv I.pVM (a := h.S.cf.lgk) (b := h.S.cf.lgk + (h.S.lnT - 1)) (by rw [I.rVM]; omega)
  obtain ⟨sVs, wVs⟩ := cutv I.pVM (a := h.S.cf.lgk + (h.S.lnT - 1)) (b := h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)
    (by rw [I.rVM]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls)
      (sh X.xM (h.S.cf.lgk + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1))))
      (psiRow (L5.dimOf h.S) (sh X.xM h.S.cf.lgk) (sh X.xM (h.S.cf.lgk + (L5.dimOf h.S).lP))
        (zi' (L5.dimOf h.S) C X.zM)))
    rw [e1, e2, I.zM, scoreTiles_fm h.S I.segM]
    exact longW_of Nn sMc wMc (tok_tile Nn
      (fun J hJ => tiles_row ρ Z (sMP.trans (by omega)) (sMs.trans (by omega)) (fun j hj => wMP j (by omega))
        (fun j hj => wMs j (by omega)) hJ) I.siM I.iM)
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls)
      (sh X.xM (h.S.cf.lgk + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1))))
      (psiCol (L5.dimOf h.S) (sh X.xM h.S.cf.lgk) (sh X.xM (h.S.cf.lgk + (L5.dimOf h.S).lP))
        (zj' (L5.dimOf h.S) C X.zM)))
    rw [e1, e2, I.zM, scoreTiles_fm h.S I.segM]
    exact longW_of Nn sMc wMc (tok_tile Nn
      (fun J hJ => tiles_col ρ Z (sMP.trans (by omega)) (sMs.trans (by omega)) (fun j hj => wMP j (by omega))
        (fun j hj => wMs j (by omega)) hJ) I.sjM I.jM)
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls)
      (sh X.xD (h.S.cf.lgk + ((L5.dimOf h.S).lP + 1))))
      (psiDiag (L5.dimOf h.S) (sh X.xD h.S.cf.lgk) (zi' (L5.dimOf h.S) C X.zD)))
    rw [e3, I.zD, scoreTiles_fd h.S I.segD]
    exact longW_of Nn sDc wDc (tok_tile Nn hDI I.siD I.iD)
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls)
      (sh X.xD (h.S.cf.lgk + ((L5.dimOf h.S).lP + 1))))
      (psiDiag (L5.dimOf h.S) (sh X.xD h.S.cf.lgk) (zj' (L5.dimOf h.S) C X.zD)))
    rw [e3, I.zD, scoreTiles_fd h.S I.segD]
    exact longW_of Nn sDc wDc (tok_tile Nn hDI I.sjD I.jD)
  · show LongW ρ h _ _ (.long (eqN h.S.ls (h.S.cf.ldh - h.S.ls) (yn (L5.dimOf h.S) C X.zVM))
      (psiCol (L5.dimOf h.S) (sh X.xVM h.S.cf.lgk) (sh X.xVM (h.S.cf.lgk + (L5.dimOf h.S).lP))
        (sh X.xVM (h.S.cf.lgk + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1)))))
    rw [e1, I.zVM, I.wJv]
    exact longW_of Nn I.scW I.nW (tok_tile Nn
      (fun J hJ => tiles_col ρ Z (sVP.trans (by omega)) (sVs.trans (by omega)) (fun j hj => wVP j (by omega))
        (fun j hj => wVs j (by omega)) hJ) sVl wVl)

/-- **WeightsAre, paid**, at the letters X. -/
theorem weights_at (I : XiIs ρ h kM kD zx C X) : WeightsAre ρ h kM kD zx TB := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := w_rows I
  obtain ⟨c1, c2, c3⟩ := w_cols I
  obtain ⟨a1, a2, a3, a4, a5⟩ := w_long_eq I
  obtain ⟨b1, b2, b3, b4, b5⟩ := w_long_tile I
  exact ⟨r1, r2, r3, r4, r5, r6, r7, r8, b1, b2, b3, b4, a2, b5, a5, a3, a4, a1, c1, c2, c3⟩

end K5Law
