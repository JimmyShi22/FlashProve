-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/BackAll.lean: kind K5: port_cl (Claims/PortAll.lean) the other way
round: where the library's ledger ownCl L Q u holds at
the early entries P.msg m and the late entries read off the world (uAt), and the eight written rows
are worth 0, the claims say what they say.

Main names:
  `parts_of_ownCl`, `plainCl_back`, `linCl_back`, `clM_ends` … `clH_ends`: the ledger taken apart.
  `RowsZero`: the eight written rows are worth 0.
  `plane_back`, `back_pM`, `back_pD`, `back_uM`, `back_uD`, `back_s5` … `back_s8`: part by part.
  `say_back`: the two plane claims (PlanesSay), the two units (UnitAt) and Say5 … Say8.
  `ownCl_of_pull_agree`: under Cb.Sub.Agree the pull-backs' holding is the ledger's holding at the
    late entries.
  `rowsHold_back`: the eight sumchecks' first output claims, out of the ledger.

Premises of say_back: those of port_cl, but Say and the four says of SixSay, which are the
conclusion; RowsZero.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.BackParts
import Johnson.Desc.First.Att.Claims.PortAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset Cb
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub Step yn Dim zg zgD Reg Fam KSc)
open Cb.Pv.Att (OwnPar ptBelow size18)
open Cb.Pv.Att.End (LateLay AttTab EndLay JoinLay Fits ptN rowF endF plainCl linCl linF rvF ptOn ownCl joinF lineF attA zT
  clM0 clM clD0 clD clE0 clE clVM clVD clM6 clF clK clH nameM nameD nameE nameU mem_pairs mem_firsts mem_ends18 LinGood)

variable {Kf : Type} [Field Kf] [Fintype Kf] {M X : Type} {J₂ : Type} [Fintype J₂] [DecidableEq J₂]
variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {P : OwnPar Kf M X} {L : EndLay P J₂} {Q : JoinLay P} {u : P.Run} {m : M}

/-- The ledger's fourteen parts hold where it holds. -/
theorem parts_of_ownCl {x : P.J ⊕ J₂ → Kf} (H : ∀ f ∈ ownCl L Q u, f.Holds x) :
    (∀ f ∈ clM0 L u, f.Holds x) ∧ (∀ f ∈ clM L u, f.Holds x) ∧ (∀ f ∈ clD0 L u, f.Holds x) ∧
    (∀ f ∈ clD L u, f.Holds x) ∧ (∀ f ∈ clE0 L u, f.Holds x) ∧ (∀ f ∈ clE L u, f.Holds x) ∧
    (joinF (J₂ := J₂) Q u).Holds x ∧ (lineF (J₂ := J₂) u).Holds x ∧
    (∀ f ∈ clVM L u, f.Holds x) ∧ (∀ f ∈ clVD L u, f.Holds x) ∧ (∀ f ∈ clM6 L u, f.Holds x) ∧
    (∀ f ∈ clF L u, f.Holds x) ∧ (∀ f ∈ clK L u, f.Holds x) ∧ (∀ f ∈ clH L u, f.Holds x) := by
  have key : ∀ f, (f ∈ clM0 L u ∨ f ∈ clM L u ∨ f ∈ clD0 L u ∨ f ∈ clD L u ∨ f ∈ clE0 L u ∨ f ∈ clE L u ∨
      f = joinF Q u ∨ f = lineF u ∨ f ∈ clVM L u ∨ f ∈ clVD L u ∨ f ∈ clM6 L u ∨ f ∈ clF L u ∨ f ∈ clK L u ∨
      f ∈ clH L u) → f.Holds x := by
    intro f hf
    refine H f ?_
    unfold ownCl
    simp only [List.mem_append, List.mem_cons]
    exact hf
  exact ⟨fun f h => key f (.inl h),
    fun f h => key f (.inr (.inl h)),
    fun f h => key f (.inr (.inr (.inl h))),
    fun f h => key f (.inr (.inr (.inr (.inl h)))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inl h))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
    key _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))),
    key _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))))),
    fun f h => key f (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))))))))⟩

/-- The row and the listed end values. -/
theorem plainCl_back {T : Cb.Pv.Att.PlainSc Kf} [DecidableEq T.J] (o : T.our.par.Out) (l : List T.A)
    (r : T.A → TWhole.Aff Kf (T.J ⊕ J₂)) (x : T.J ⊕ J₂ → Kf) (H : ∀ f ∈ plainCl T o l r, f.Holds x) :
    ∀ a ∈ l, (endF T o a (r a)).Holds x := fun _ ha =>
  H _ (List.mem_cons_of_mem _ (List.mem_map_of_mem ha))

omit [Fintype Kf] in
theorem linCl_back {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {D : Dim} {C : Calls} {ls lmS : ℕ} {Y : LateLay AttTab J₂}
    {name : ℕ → Option KSc} {n : ℕ} {r : Fin n → Kf} {kk : Fin n → J₁} {z : ℕ → Kf} {x : J₁ ⊕ J₂ → Kf}
    (H : ∀ f ∈ linCl D C ls lmS Y name r kk z, f.Holds x) (j : Fin n) (k : KSc) (hn : name j.val = some k) :
    (linF (r j) (kk j) (rvF D C ls lmS Y z k)).Holds x := by
  refine H _ ?_
  unfold linCl
  refine List.mem_filterMap.2 ⟨j, List.mem_finRange j, ?_⟩
  rw [hn]
  rfl

theorem nameU_cell (f : Fam) (r : Reg) {y : ℕ} (hy : y < 5) : nameU f r y = some (.cell f y) := by
  interval_cases y <;> rfl

/-- The eight written rows are worth 0. -/
structure RowsZero (ρ : Reading Kf) (W : World Kf) (h : Attention.Heard) (s : Six) : Prop where
  rM : s.kM.sc.rowU.value ρ W = 0
  rD : s.kD.sc.rowU.value ρ W = 0
  rE : h.d.scE.rowU.value ρ W = 0
  rVM : h.d.vpm.rowU.value ρ W = 0
  rVD : h.d.vpd.rowU.value ρ W = 0
  rF : h.x.scF.rowU.value ρ W = 0
  rK : h.x.scd.rowU.value ρ W = 0
  rH : h.x.scH.rowU.value ρ W = 0

variable {tabOf : AttTab → ℕ} {ul : J₂ → Kf}

local notation "XX" => Sum.elim (P.msg m) ul

/-- A plane value of a plane claim, backwards. -/
theorem plane_back {h : Attention.Heard} (Z : SizesAre P L h) (LA : LateAt W h K3 L.Y tabOf (placeAtt h.S) ul)
    (hG : LinGood P.D L.ls L.lmS L.Y) (hT : tabOf .tA = h.t.tA) {z : ℕ → Kf} {fam : Fam} {pc : PlaneClaim}
    (Q' : PlanePts ρ h P.D P.C z fam pc) {x : ℕ} (hx5 : x < 5)
    {r : Kf} {k : P.J} (hs : W.slot (pc.s0 + x) = r - P.msg m k)
    (H : (linF r k (rvF P.D P.C L.ls L.lmS L.Y z (.cell fam x))).Holds XX) :
    (Fo.planeMember h K3 pc x).value ρ W = 0 :=
  cellF_bk Z.D Z.ls Z.lmS LA P.C z hG r k fam Q'.plane x hx5 hT Q'.pairs Q'.reg Q'.nb Q'.size Q'.vz Q'.w hs H

/-! ### the listed end values of the eight sumchecks, out of the ledger's parts -/

section Ends
open Cb.Pv.Att.End (pick pairs firsts ends18 rA6b rB6b rA6d rB6d rA8 rB8 rA11 rB11 rA12 rB12 rA16 keyR bitsR)
variable {x : P.J ⊕ J₂ → Kf}

theorem clM_ends (H : ∀ f ∈ clM L u, f.Holds x) (a : Fin P.D.nb × Bool) :
    (endF P.uM.T u.oM a (pick (rA6b P.D L.ls L.Y (ptN P.uM.T u.oM)) (rB6b P.D L.ls L.Y (ptN P.uM.T u.oM)) a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_pairs a, rfl⟩))

theorem clD_ends (H : ∀ f ∈ clD L u, f.Holds x) (a : Fin P.D.nb × Bool) :
    (endF P.uD.T u.oD a (pick (rA6d P.D L.ls L.Y (ptN P.uD.T u.oD)) (rB6d P.D L.ls L.Y (ptN P.uD.T u.oD)) a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_pairs a, rfl⟩))

theorem clE_ends (H : ∀ f ∈ clE L u, f.Holds x) (a : Fin P.D.nb × Bool) :
    (endF P.sE.T u.oE a (pick (rA8 P.D L.Y (ptN P.sE.T u.oE)) (rB8 P.D P.C L.ls L.Y u.oE.st (ptN P.sE.T u.oE)) a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_pairs a, rfl⟩))

theorem clVM_ends (H : ∀ f ∈ clVM L u, f.Holds x) (a : Fin P.D.nb × Bool) :
    (endF P.sVM.T u.oVM a (pick (rA11 P.D P.C L.lmS L.Y u.oVM.st (ptN P.sVM.T u.oVM))
      (rB11 P.D P.C L.ls L.Y u.oVM.st (ptN P.sVM.T u.oVM)) a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_pairs a, rfl⟩))

theorem clVD_ends (H : ∀ f ∈ clVD L u, f.Holds x) (a : Fin P.D.nb × Bool) :
    (endF P.sVD.T u.oVD a (pick (rA12 P.D P.C L.lmS L.Y u.oVD.st (ptN P.sVD.T u.oVD))
      (rB12 P.D P.C L.ls L.Y u.oVD.st (ptN P.sVD.T u.oVD)) a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_pairs a, rfl⟩))

theorem clF_ends (H : ∀ f ∈ clF L u, f.Holds x) (b : Fin P.D.nb) :
    (endF P.sF.T u.oF (b, false) (rA16 P.D L.ls L.Y (ptN P.sF.T u.oF) b.val)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨(b, false), mem_firsts b, rfl⟩))

theorem clK_ends (H : ∀ f ∈ clK L u, f.Holds x) (a : (size18 P.D).A) :
    (endF P.sD.T u.oK a (keyR P.D L.ls L.Y (Prod.fst u.oK.st) (ptN P.sD.T u.oK) a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_ends18 a, rfl⟩))

theorem clH_ends (H : ∀ f ∈ clH L u, f.Holds x) (a : Fin P.D.nb × Bool) :
    (endF P.sH.T u.oH a (bitsR P.D L.Y P.rd (fun _ _ => 0) P.kap P.cH P.wH u.oH a)).Holds x :=
  H _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, mem_pairs a, rfl⟩))

end Ends

/-! ### the ledger's parts, backwards -/

theorem back_pM {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (F : Fits L Q) (nM : s.pM.np = 3)
    (Pt : PtsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (a1 : ∀ f ∈ clM0 L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) : PlanesSay ρ W h K3 s.pM := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  intro y hy
  rw [nM] at hy
  have hj : y < 3 * P.npl + 7 := by omega
  exact plane_back Z LA F.gLin (tabOf_six h).1 Pt.pM (by omega) (Sl.m1 ⟨y, hj⟩ hy)
    (linCl_back a1 ⟨y, hj⟩ (.cell .m1 y) (by show nameM y = _; unfold nameM; rw [if_pos hy]))

theorem back_pD {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (F : Fits L Q) (nD : s.pD.np = 3)
    (Pt : PtsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (a1 : ∀ f ∈ clM0 L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) : PlanesSay ρ W h K3 s.pD := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  intro y hy
  rw [nD] at hy
  have hj : 3 + y < 3 * P.npl + 7 := by omega
  have e := Sl.m2 ⟨3 + y, hj⟩ (Nat.le_add_right 3 y) (by show 3 + y < 6; omega)
  rw [show (⟨3 + y, hj⟩ : Fin (3 * P.npl + 7)).val - 3 = y from Nat.add_sub_cancel_left 3 y] at e
  exact plane_back Z LA F.gLin (tabOf_six h).1 Pt.pD (by omega) e
    (linCl_back a1 ⟨3 + y, hj⟩ (.cell .d1 y) (by
      show nameM (3 + y) = _
      unfold nameM
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]))

theorem back_uM {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (iM : InUnit h s.kM (h.t.score.getD 0 default)) (nUM : s.cM.np = 5) (s0M : s.cM.s0 = s.kM.s0)
    (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (rM : s.kM.sc.rowU.value ρ W = 0)
    (a1 : ∀ f ∈ clM0 L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a2 : ∀ f ∈ clM L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) :
    UnitAt ρ W h K3 s.kM (h.t.score.getD 0 default) s.cM := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  have hnp := F.npl
  have slM : ∀ y (hy : y < 7), W.slot (s.kM.s0 + y) =
      u.rM ⟨6 + y, by omega⟩ - P.msg m (P.kM ⟨6 + y, by omega⟩) := by
    intro y hy
    have hj : 6 + y < 3 * P.npl + 7 := by omega
    have e := Sl.m3 ⟨6 + y, hj⟩ (Nat.le_add_right 6 y)
    rw [show (⟨6 + y, hj⟩ : Fin (3 * P.npl + 7)).val - 6 = y from Nat.add_sub_cancel_left 6 y] at e
    exact e
  have nmM : ∀ y, nameM (6 + y) = nameU .m2 .M y := by
    intro y
    unfold nameM
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
  refine ⟨fun y hy => ?_, ?_, rM, ?_⟩
  · rw [nUM] at hy
    have hs : W.slot (s.cM.s0 + y) = u.rM ⟨6 + y, by omega⟩ - P.msg m (P.kM ⟨6 + y, by omega⟩) := by
      rw [s0M]
      exact slM y (by omega)
    exact plane_back Z LA F.gLin (tabOf_six h).1 Pt.cM hy hs
      (linCl_back a1 ⟨6 + y, by omega⟩ (.cell .m2 y) (by show nameM (6 + y) = _; rw [nmM, nameU_cell _ _ hy]))
  · have hH := linCl_back a1 ⟨6 + 5, by omega⟩ (.ms .M) (by show nameM (6 + 5) = _; rw [nmM]; rfl)
    exact msMF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ (tabOf_six h).2.2.2.2.1 Pt.xM.pairs Pt.xM.size Pt.xM.vg
      Pt.xM.w (slM 5 (by omega)) hH
  · exact unitMF_bk Z.D Z.ls A LA rfl rfl P.C u.oM iM Pt.xM.pairs N.q2 N.k2 O.rM O.xM F.g6b Sl.eM
      (clM_ends a2)

theorem back_uD {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (iD : InUnit h s.kD (h.t.score.getD 1 default)) (nUD : s.cD.np = 5) (s0D : s.cD.s0 = s.kD.s0)
    (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (rD : s.kD.sc.rowU.value ρ W = 0)
    (a3 : ∀ f ∈ clD0 L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a4 : ∀ f ∈ clD L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) :
    UnitAt ρ W h K3 s.kD (h.t.score.getD 1 default) s.cD := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  refine ⟨fun y hy => ?_, ?_, rD, ?_⟩
  · rw [nUD] at hy
    have hs : W.slot (s.cD.s0 + y) = u.rD ⟨y, by omega⟩ - P.msg m (P.kD ⟨y, by omega⟩) := by
      rw [s0D]
      exact Sl.d ⟨y, by omega⟩
    exact plane_back Z LA F.gLin (tabOf_six h).1 Pt.cD hy hs
      (linCl_back a3 ⟨y, by omega⟩ (.cell .d2 y) (by show nameD y = _; unfold nameD; exact nameU_cell _ _ hy))
  · have hH := linCl_back a3 ⟨5, by omega⟩ (.ms .D) rfl
    exact msDF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ (tabOf_six h).2.2.2.2.2 Pt.xD.pairs Pt.xD.size Pt.xD.vg
      Pt.xD.w (Sl.d ⟨5, by omega⟩) hH
  · exact unitDF_bk Z.D Z.ls A LA rfl rfl P.C u.oD iD Pt.xD.pairs N.q2 N.k2 O.rD O.xD F.g6d Sl.eD
      (clD_ends a4)

theorem back_s5 {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (I : InTail h) (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (rE : h.d.scE.rowU.value ρ W = 0)
    (a5 : ∀ f ∈ clE0 L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a6 : ∀ f ∈ clE L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) : Say5 ρ W h K3 := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  have hlT : P.D.lT = h.S.cf.lt := by rw [Z.D]; exact pub_lT A
  have slE : ∀ j (hj : j < 5 + P.D.lT + 2), W.slot (slotEh h P.D.lT j) = u.rE ⟨j, hj⟩ - P.msg m (P.kE ⟨j, hj⟩) :=
    fun j hj => Sl.e ⟨j, hj⟩
  obtain ⟨_, tW, tX, tO, _, _⟩ := tabOf_six h
  refine ⟨?_, ?_, ?_, fun k hk => ?_, ?_, ?_, rE, ?_⟩
  · have e := slE 2 (by omega)
    unfold slotEh at e
    rw [if_pos (by omega)] at e
    have hH := linCl_back a5 ⟨2, by omega⟩ .zc (by show nameE P.D 2 = _; unfold nameE; simp)
    exact zcF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ tW Pt.dv.pW Pt.dv.gW Pt.dv.vgW Pt.dv.wW e hH
  · have e := slE 3 (by omega)
    unfold slotEh at e
    rw [if_pos (by omega)] at e
    have hH := linCl_back a5 ⟨3, by omega⟩ .rh (by show nameE P.D 3 = _; unfold nameE; simp)
    exact highF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ true .w3 tO Pt.dv.pW Pt.dv.gW Pt.dv.cW Pt.dv.vgW
      Pt.dv.vnW Pt.dv.wW (Pt.dv.fe true _ (.inl rfl)) e hH
  · have e := slE 4 (by omega)
    unfold slotEh at e
    rw [if_pos (by omega)] at e
    have hH := linCl_back a5 ⟨4, by omega⟩ .rh' (by show nameE P.D 4 = _; unfold nameE; simp)
    exact highF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ false .w3 tO Pt.dv.pW Pt.dv.gW Pt.dv.cW Pt.dv.vgW
      Pt.dv.vnW Pt.dv.wW (Pt.dv.fe false _ (.inl rfl)) e hH
  · have e := slE (5 + k) (by omega)
    unfold slotEh at e
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left] at e
    have hH := linCl_back a5 ⟨5 + k, by omega⟩ (.ib k) (by
      show nameE P.D (5 + k) = _
      unfold nameE
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left])
    exact ibF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ k (by omega) tX Pt.dv.pX Pt.dv.gX Pt.dv.vgX Pt.dv.wX e hH
  · have e := slE (5 + P.D.lT) (by omega)
    unfold slotEh at e
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, Nat.add_zero] at e
    have hH := linCl_back a5 ⟨5 + P.D.lT, by omega⟩ .rg (by
      show nameE P.D (5 + P.D.lT) = _
      unfold nameE
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos rfl])
    exact highF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ true .f4 tO Pt.dv.pH Pt.dv.gH Pt.dv.cH Pt.dv.vgH
      Pt.dv.vnH Pt.dv.wH (Pt.dv.fe true _ (.inr rfl)) e hH
  · have e := slE (5 + P.D.lT + 1) (by omega)
    unfold slotEh at e
    rw [if_neg (by omega), if_neg (by omega), show 5 + P.D.lT + 1 - (5 + P.D.lT) = 1 by omega] at e
    have hH := linCl_back a5 ⟨5 + P.D.lT + 1, by omega⟩ .rg' (by
      show nameE P.D (5 + P.D.lT + 1) = _
      unfold nameE
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl])
    exact highF_bk Z.D Z.ls Z.lmS A LA P.C (zT u) F.gLin _ _ false .f4 tO Pt.dv.pH Pt.dv.gH Pt.dv.cH Pt.dv.vgH
      Pt.dv.vnH Pt.dv.wH (Pt.dv.fe false _ (.inr rfl)) e hH
  · exact productF_bk Z.D Z.ls A LA rfl rfl P.C u.oE I Pt.dv.pW N.o2 O.rE Pt.dv.cW O.xE O.ynE F.g8 Sl.eE
      (clE_ends a6)

theorem back_s6 {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (I : InTail h) (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (rVM : h.d.vpm.rowU.value ρ W = 0) (rVD : h.d.vpd.rowU.value ρ W = 0)
    (a8 : (lineF (J₂ := J₂) u).Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a9 : ∀ f ∈ clVM L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a10 : ∀ f ∈ clVD L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) : Say6 ρ W h K3 := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  have Tb := lateTabs_att h
  have e2 : W.slot h.d.sACC = u.rE P.iACC - P.msg m (P.kE P.iACC) := by
    have e := Sl.e P.iACC
    unfold slotEh at e
    rw [if_pos (by show (0 : ℕ) < 5; norm_num)] at e
    exact e
  have e3 : W.slot h.d.sZC = u.rE P.iZC - P.msg m (P.kE P.iZC) := by
    have e := Sl.e P.iZC
    unfold slotEh at e
    rw [if_pos (by show (2 : ℕ) < 5; norm_num)] at e
    exact e
  exact ⟨lineF_bk _ _ _ _ _ _ _ _ _ Sl.v0 Sl.v1 e2 e3 O.th a8,
    ⟨rVM, belowF_bk Z.D Z.ls Z.lmS A LA rfl rfl P.C u.oVM I Pt.dv.pW N.v2 N.nM N.ptM O.rVM Pt.dv.cW O.xVM O.ptVM
      O.ynVM O.thVM F.g11 Sl.eVM (clVM_ends a9)⟩,
    ⟨rVD, onF_bk Z.D Z.ls Z.lmS A LA Tb P.C u.oVD I Pt.dv.pW N.v2 N.nD N.ptD O.rVD Pt.dv.cW O.xVD O.ptVD
      O.ynVD O.thVD F.g12 Sl.eVD (clVD_ends a10)⟩⟩

theorem back_s7 {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (I : InTail h) (O : OutsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (rF : h.x.scF.rowU.value ρ W = 0) (rK : h.x.scd.rowU.value ρ W = 0)
    (a11 : ∀ f ∈ clM6 L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a12 : ∀ f ∈ clF L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (a13 : ∀ f ∈ clK L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) : Say7 ρ W h K3 := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  have Tb := lateTabs_att h
  have hnb : P.D.nb = h.S.NP := by rw [Z.D]; rfl
  refine ⟨fun b hb => ?_, rF, ?_, rK, ?_⟩
  · have hb' : b < P.D.nb := by rw [hnb]; exact hb
    refine m6F_bk (m := P.msg m) (u := (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))) Z.D A LA Tb (P.pubZ u.z) O.tg O.vtg
      F.gM (fun c => if hc : c < P.D.nb then u.s ⟨c, hc⟩ else 0)
      (fun c => if hc : c < P.D.nb then P.kF ⟨c, hc⟩ else P.kF ⟨b, hb'⟩) (fun c hc => ?_) (fun c hc => ?_) b hb
    · have hc' : c < P.D.nb := by rw [hnb]; exact hc
      beta_reduce
      rw [dif_pos hc', dif_pos hc']
      exact Sl.f ⟨c, hc'⟩
    · have hc' : c < P.D.nb := by rw [hnb]; exact hc
      beta_reduce
      rw [dif_pos hc', dif_pos hc']
      refine a11 _ ?_
      unfold clM6
      exact List.mem_map.2 ⟨⟨c, hc'⟩, List.mem_finRange _, rfl⟩
  · exact scoreF_bk Z.D Z.ls A LA Tb P.C u.oF I N.q2 O.rF O.xF F.g16 Sl.eF
      (clF_ends a12)
  · exact keyF_bk Z.D Z.ls A LA Tb Prod.fst Prod.snd u.oK I N.k2 O.rF O.rK O.xK O.fn F.g18 Sl.eK Sl.eB
      (clK_ends a13)

theorem back_s8 {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (O : OutsAre ρ h P u s) (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))
    (rH : h.x.scH.rowU.value ρ W = 0)
    (a14 : ∀ f ∈ clH L u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) : Say8 ρ W h K3 :=
  ⟨rH, bitsF_bk Z.D Z.kap A (late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)) (lateTabs_att h) u.oH O.rH O.xH F.gH Sl.eH
    (clH_ends a14)⟩

/-- **port_cl backwards.** -/
theorem say_back {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (I : InTail h) (iM : InUnit h s.kM (h.t.score.getD 0 default))
    (iD : InUnit h s.kD (h.t.score.getD 1 default)) (nM : s.pM.np = 3) (nD : s.pD.np = 3) (nUM : s.cM.np = 5)
    (nUD : s.cD.np = 5) (s0M : s.cM.s0 = s.kM.s0) (s0D : s.cD.s0 = s.kD.s0)
    (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s)
    (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))) (R : RowsZero ρ W h s)
    (H : ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) :
    PlanesSay ρ W h K3 s.pM ∧ PlanesSay ρ W h K3 s.pD ∧
      UnitAt ρ W h K3 s.kM (h.t.score.getD 0 default) s.cM ∧ UnitAt ρ W h K3 s.kD (h.t.score.getD 1 default) s.cD ∧
      Say5 ρ W h K3 ∧ Say6 ρ W h K3 ∧ Say7 ρ W h K3 ∧ Say8 ρ W h K3 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, _, a8, a9, a10, a11, a12, a13, a14⟩ := parts_of_ownCl H
  exact ⟨back_pM s Z F nM Pt Sl a1, back_pD s Z F nD Pt Sl a1, back_uM s Z A F N iM nUM s0M Pt O Sl R.rM a1 a2,
    back_uD s Z A F N iD nUD s0D Pt O Sl R.rD a3 a4, back_s5 s Z A F N I Pt O Sl R.rE a5 a6,
    back_s6 s Z A F N I Pt O Sl R.rVM R.rVD a8 a9 a10, back_s7 s Z A F N I O Sl R.rF R.rK a11 a12 a13,
    back_s8 s Z A F O Sl R.rH a14⟩

/-- Under the library's Agree the pull-backs' holding is the ledger's, at the late entries ul. -/
theorem ownCl_of_pull_agree {ul' : J₂ → Kf} (hA : Cb.Sub.Agree (attA L u) (P.msg m) ul')
    (hh : ∀ f ∈ ownCl L Q u, (Cb.Sub.pullF (attA L u) f).Holds (P.msg m)) :
    ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) ul') := by
  have e : ul' = fun i => (attA L u i).val (P.msg m) := funext hA
  rw [e]
  exact fun f hf => (Cb.Sub.pullF_holds _ f _).1 (hh f hf)

/-- The eight sumchecks' first output claims, out of the ledger. -/
theorem rowsHold_back {ul' : J₂ → Kf} (H : ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) ul')) : RowsHold P u m := by
  obtain ⟨_, a2, _, a4, _, a6, _, _, a9, a10, _, a12, a13, a14⟩ := parts_of_ownCl H
  exact ⟨(rowF_holds _ _ _).1 (a2 _ List.mem_cons_self), (rowF_holds _ _ _).1 (a4 _ List.mem_cons_self),
    (rowF_holds _ _ _).1 (a6 _ List.mem_cons_self), (rowF_holds _ _ _).1 (a9 _ List.mem_cons_self),
    (rowF_holds _ _ _).1 (a10 _ List.mem_cons_self), (rowF_holds _ _ _).1 (a12 _ List.mem_cons_self),
    (rowF_holds _ _ _).1 (a13 _ List.mem_cons_self), (rowF_holds _ _ _).1 (a14 _ List.mem_cons_self)⟩

end K5Law

#print axioms K5Law.say_back
