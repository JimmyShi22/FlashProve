-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortMine.lean: kind K5: four of the records that port_cl
(Johnson/Desc/First/Att/Claims/PortAll.lean) takes, paid or turned at a record of the kind's own, h
:= oldOf S gL i (Johnson/Desc/First/Att/Claims/Any.lean).

Main names:
  `shape_nums`: ShapeNums P h, from the planner's shape (AttPub), the two points' texts (ptM =
    pointM, ptD = pointD: tabs_at, Johnson/Desc/First/Att/Claims/TablesAt.lean) and three lengths
    (of vpm.r, vpd.r and ziW).
  `rems_visited`; `sixAt g zk r1 r2 a1 a2 k1 k2 u1 u2`: the six, of the kind's own records;
    `six_say`: SixSay, from the return of pointsOf and of the two runs and "every gathered form is
    worth 0".
  `say_tail_at`: Say and InTail.
  `nth_of_map`; `slotsH_of`: SlotsH … (sixAt …) ul from the same facts in the hearing's numbers
    (five, bits, two, values, maxima, each sumcheck's sEnd; pl, sv, ue: where the plane messages,
    the units' seven scalars and the units' end values begin; the numberings sc3Num and scdNum).
Premises of six_say beyond the runs' return: the place has just two remainder-table units and two
softmax-table units (Geo.units .kr [.rm, .rd] = [r1, r2]; Geo.scores = [u1, u2]); S.G = 2 ^ lgk. Not
shown in this file or in what it imports.
Used: as Johnson/Desc/First/Att/Claims/PortAll.lean, and norm_of_hid, sizes_of_hid, sizeCut,
Attention.pointM, pointD, lastCoords; OnBytes.Tie.Pv.Att.sc3Num and scdNum (pure functions).

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.Sc3Top
import Johnson.Desc.First.Att.Claims.PortAll
import Johnson.Desc.First.Att.Claims.PlanesAre
import Johnson.Desc.First.Att.Claims.SayAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law

section Nums
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (EndLay)

variable {Kf : Type} [Field Kf] [Fintype Kf] {M X : Type} {J₂ : Type}
  {ρ : Reading Kf} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {P : OwnPar Kf M X} {L : EndLay P J₂} {h : Attention.Heard}

/-- **The eight numbers of the shape**, from the planner's shape, the two points' texts and three lengths. -/
theorem shape_nums (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (hM : h.t.ptM = pointM h.S h.d)
    (hD : h.t.ptD = pointD h.S h.d) (rM : h.d.vpm.r.size = h.S.nvVM) (rD : h.d.vpd.r.size = h.S.nvVD)
    (hzi : h.d.ziW.size = h.S.cf.lt) : ShapeNums P h := by
  have N := norm_of_hid A.shape
  have Zs := sizes_of_hid A.shape
  have hl := Zs.lnT
  have hlt := N.lt
  have rM' : h.d.vpm.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB := rM
  have rD' : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB := rD
  have q2 : (h.d.zilo h.S).size = h.S.cf.lB := by
    unfold Attention.Divide.zilo
    rw [sizeCut _ (by omega)]
    omega
  refine ⟨by rw [N.atQ], by rw [N.atK], by rw [N.atV], by rw [N.atO], by rw [Z.D]; exact N.nM.symm,
    by rw [Z.D]; exact N.nD.symm, ?_, ?_⟩
  · have q1 : (h.d.vpm.r.extract 0 (h.S.cf.lgk + 2 * h.S.lnT - 1)).size =
        h.S.cf.lgk + 2 * h.S.lnT - 1 := by
      rw [sizeCut _ (by omega)]
      omega
    have q3 : (lastCoords h.d.vpm.r h.S.cf.lB).size = h.S.cf.lB := by
      unfold Attention.lastCoords
      rw [sizeCut _ (Nat.le_refl _)]
      omega
    rw [hM, N.nM]
    unfold Attention.pointM
    rw [Array.size_append, Array.size_append, q1, q2, q3]
    omega
  · have q1 : (h.d.vpd.r.extract 0 (h.S.cf.lgk + h.S.lnT)).size = h.S.cf.lgk + h.S.lnT := by
      rw [sizeCut _ (by omega)]
      omega
    have q3 : (lastCoords h.d.vpd.r h.S.cf.lB).size = h.S.cf.lB := by
      unfold Attention.lastCoords
      rw [sizeCut _ (Nat.le_refl _)]
      omega
    rw [hD, N.nD]
    unfold Attention.pointD
    rw [Array.size_append, Array.size_append, q1, q2, q3]
    omega
end Nums

section SixS
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG Keys UnitG ScoreP RemP geoOf callOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

/-- Each remainder-table unit's call is a remainder-table call of the place. -/
theorem rems_visited (g : Geo) (ks : List Keys) : ∀ u ∈ g.units .kr ks,
    (u.2.1, u.1) ∈ g.calls.toList.zipIdx ∧ (u.2.1.tab == P.Tab.kr) = true := by
  intro u hu
  unfold P.Geo.units at hu
  simp only [List.mem_flatMap] at hu
  obtain ⟨x, hx, hv⟩ := hu
  by_cases hc : (x.1.tab == P.Tab.kr) = true
  · rw [if_pos hc] at hv
    simp only [List.mem_map] at hv
    obtain ⟨k, _, rfl⟩ := hv
    exact ⟨hx, hc⟩
  · rw [if_neg hc] at hv
    cases hv

/-- The six, of the kind's own records. -/
def sixAt (g : Geo) (zk : Array (Array E)) (r1 r2 : ℕ × CallG × Keys) (a1 a2 : ℕ) (k1 k2 : ScoreP)
    (u1 u2 : UnitG) : Six :=
  ⟨remBack (remAt g zk r1 a1), remBack (remAt g zk r2 a2), scoreBack k1, scoreBack k2,
    remBack (remOfUnit zk u1 k1.s0), remBack (remOfUnit zk u2 k2.s0)⟩

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {S : Attention.Shape} {gL : Forest.Heard}
  {i : P.Runs.In} {K : ℕ} {l₁ l₂ : List Aff} {j : JoinsP}

/-- **What the claims say of the six**, at a record of the kind's own whose place has two remainder-table units and two softmax-table units. -/
theorem six_say (A : Plan) {zk : Array (Array E)} {hh : P.Heard} {L : P.Left}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (hP : P.pointsOf i.g zk hh L = some i.p)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (hZ : AllZero ρ W (l₁ ++ l₂)) (hG : S.G = 2 ^ S.cf.lgk)
    {r1 r2 : ℕ × CallG × Keys} (hkr : i.g.units .kr [.rm, .rd] = [r1, r2])
    {u1 u2 : UnitG} (hgs : i.g.scores = [u1, u2]) :
    ∃ a1 a2 k1 k2, hh.remainders[0]? = some a1 ∧ hh.remainders[1]? = some a2 ∧
      i.p.scores[0]? = some k1 ∧ i.p.scores[1]? = some k2 ∧
      SixSay ρ W (oldOf S gL i) K (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2) := by
  have PA := points_are hP
  have Pl := planes_are hP
  have Sy := (say_at Kf ρ W A S gL i K l₁ l₂ j hg hz hN (units_visited PA) h1 h2).1 hZ
  have R := runs_at_old (gL := gL) hg hz h1 h2
  have nR : hh.remainders.size = 2 := by rw [← Pl.nR, hkr]; rfl
  have nH : hh.scores.size = 2 := by rw [← PA.nH, hgs]; rfl
  have ea1 : hh.remainders[0]? = some hh.remainders[0] := Array.getElem?_eq_getElem (by omega)
  have ea2 : hh.remainders[1]? = some hh.remainders[1] := Array.getElem?_eq_getElem (by omega)
  have eo1 : hh.scores[0]? = some hh.scores[0] := Array.getElem?_eq_getElem (by omega)
  have eo2 : hh.scores[1]? = some hh.scores[1] := Array.getElem?_eq_getElem (by omega)
  have p1 := Pl.rem 0 r1 _ (by rw [hkr]; rfl) ea1
  have p2 := Pl.rem 1 r2 _ (by rw [hkr]; rfl) ea2
  obtain ⟨k1, s1, _, c1, z1, _, _, _⟩ := Pl.unit 0 u1 _ (by rw [hgs]; rfl) eo1
  obtain ⟨k2, s2, _, c2, z2, _, _, _⟩ := Pl.unit 1 u2 _ (by rw [hgs]; rfl) eo2
  rw [← z1] at c1
  rw [← z2] at c2
  have planeSay : ∀ (n : ℕ) (r : ℕ × CallG × Keys) (a : ℕ), r ∈ i.g.units .kr [.rm, .rd] →
      i.p.planes[n]? = some (remAt i.g zk r a) →
      PlanesSay ρ W (oldOf S gL i) K (remBack (remAt i.g zk r a)) := by
    intro n r a hr hp
    obtain ⟨hc, ht⟩ := rems_visited i.g _ r hr
    rw [hg, calls_zip] at hc
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hc
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    refine Sy.s3 y hy ?_ _ ?_ ?_
    · rw [← tab_eq y.1.kind Table.kr]
      rw [← e1] at ht
      exact ht
    · have e3 := old_plane S gL i n
      rw [hp] at e3
      rw [← Array.getElem?_toList] at e3
      exact List.mem_of_getElem? e3
    · show (r.1 == y.2) = true
      rw [e2]
      exact beq_self_eq_true _
  have unitSay : ∀ (n : ℕ) (k : ScoreP) (u : UnitG), i.p.scores[n]? = some k →
      i.p.planes[k.claim]? = some (remOfUnit zk u k.s0) →
      UnitAt ρ W (oldOf S gL i) K (scoreBack k) ((oldOf S gL i).t.score.getD n default)
          (remBack (remOfUnit zk u k.s0)) ∧
        InUnit (oldOf S gL i) (scoreBack k) ((oldOf S gL i).t.score.getD n default) := by
    intro n k u hk hc
    have hm : (k, n) ∈ i.p.scores.toList.zipIdx :=
      List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; exact hk)
    obtain ⟨tb, pc, t1, t2, U⟩ := Sy.units (k, n) hm
    have t2' : i.p.planes[k.claim]? = some pc := t2
    rw [hc] at t2'
    rw [← Option.some.inj t2'] at U
    have et : (oldOf S gL i).t.score[n]? = some (tbBack tb) := by rw [old_score, t1]; rfl
    have eg : (oldOf S gL i).t.score.getD n default = tbBack tb := by
      rw [Array.getD_eq_getD_getElem?, et]
      rfl
    rw [eg]
    refine ⟨U, ?_⟩
    obtain ⟨c', hc', ht⟩ := units_visited PA k (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk))
    rw [hg, calls_zip] at hc'
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hc'
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    refine in_unit (oldOf S gL i) R.1 hG (c := y.1) (q := y.2) hy ?_ (k := scoreBack k) (n := n) ?_ ?_ et
    · rw [← tab_eq y.1.kind Table.kfd]
      rw [← e1] at ht
      exact ht
    · rw [old_scores_zip]
      exact List.mem_map.2 ⟨(k, n), hm, rfl⟩
    · show (k.call == y.2) = true
      rw [e2]
      exact beq_self_eq_true _
  obtain ⟨U1, I1⟩ := unitSay 0 k1 u1 s1 c1
  obtain ⟨U2, I2⟩ := unitSay 1 k2 u2 s2 c2
  exact ⟨_, _, k1, k2, ea1, ea2, s1, s2,
    ⟨planeSay 0 r1 _ (by rw [hkr]; exact List.mem_cons_self) p1,
     planeSay 1 r2 _ (by rw [hkr]; exact List.mem_cons_of_mem _ List.mem_cons_self) p2,
     U1, U2, I1, I2, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **What the claims say, and the bounds and lawful heads behind the units**, at a record of the kind's own. -/
theorem say_tail_at (A : Plan) (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (hZ : AllZero ρ W (l₁ ++ l₂)) (hG : S.G = 2 ^ S.cf.lgk) :
    Say ρ W (oldOf S gL i) K ∧ InTail (oldOf S gL i) := by
  have R := runs_at_old (gL := gL) hg hz h1 h2
  exact ⟨(say_iff Kf ρ W A S gL i K l₁ l₂ j hg hz hN h1 h2).1 hZ, in_tail (oldOf S gL i) R.1 R.2 hG⟩
end SixS

section Slots
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Tie.Pv.Att (sc3Num scdNum)
open Cb.Pv.Att (OwnPar size18)
open Cb.Pv.Att.End (EndLay)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG Keys UnitG ScoreP geoOf)

variable {Kf : Type} [Field Kf] [Fintype Kf] {M X : Type} {J₂ : Type}
  {ρ : Reading Kf} {W : World Kf} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M} {ul : J₂ → Kf}
  {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}

theorem nth_of_map {α β γ : Type} {f : α → γ} {g : β → γ} {l : List α} {l' : List β}
    (e : l.map f = l'.map g) {n : ℕ} {a : α} {b : β} (ha : l[n]? = some a) (hb : l'[n]? = some b) :
    f a = g b := by
  have e' := congrArg (·[n]?) e
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq] at e'
  exact e'

/-- **The dictionary of slots in the numbers of oldOf S gL i, from the same in the hearing's numbers.** pl · sv · ue: where the plane messages, the units' seven scalars and the units' end values begin. -/
theorem slotsH_of {zk : Array (Array E)} {hh : P.Heard} {L : P.Left} (PA : PointsAre i.g zk hh L i.p)
    (hD : Pp.D = L5.dimOf S) (A : AttPub ρ (oldOf S gL i) lid cf fs) (hnpl : Pp.npl = 2)
    {r1 r2 : ℕ × CallG × Keys} {u1 u2 : UnitG} {a1 a2 : ℕ} {k1 k2 : ScoreP}
    {o1 o2 : ℕ × VerifiableInference.Desc.Part.MaskedSum.Heard}
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (ho1 : hh.scores[0]? = some o1) (ho2 : hh.scores[1]? = some o2)
    (pl sv ue : ℕ → ℕ) (p0 : pl 0 = a1) (p1 : pl 1 = a2) (s0 : sv 0 = o1.1) (s1 : sv 1 = o2.1)
    (e0 : ue 0 = o1.2.sEnd) (e1 : ue 1 = o2.2.sEnd)
    (rM : ∀ j : Fin (3 * Pp.npl + 7), W.slot (if j.1 < 3 * Pp.npl then pl (j.1 / 3) + j.1 % 3
      else sv 0 + (j.1 - 3 * Pp.npl)) = u.rM j - Pp.msg m (Pp.kM j))
    (rD : ∀ j : Fin 7, W.slot (sv 1 + j.1) = u.rD j - Pp.msg m (Pp.kD j))
    (rE : ∀ j : Fin (5 + Pp.D.lT + 2), W.slot (if j.1 < 5 then hh.five + j.1
      else if j.1 < 5 + Pp.D.lT then hh.bits + (j.1 - 5) else hh.two + (j.1 - (5 + Pp.D.lT))) =
        u.rE j - Pp.msg m (Pp.kE j))
    (rV : ∀ j : Fin 2, W.slot (hh.values + j.1) = u.rV j - Pp.msg m (Pp.kV j))
    (rF : ∀ b : Fin Pp.D.nb, W.slot (hh.maxima + b.1) = u.s b - Pp.msg m (Pp.kF b))
    (eUM : ∀ y, SlotAt W Pp.uM.T u.oM (Sum.elim (Pp.msg m) ul) (ue 0 + sc3Num y) y)
    (eUD : ∀ y, SlotAt W Pp.uD.T u.oD (Sum.elim (Pp.msg m) ul) (ue 1 + sc3Num y) y)
    (eE : ∀ y, SlotAt W Pp.sE.T u.oE (Sum.elim (Pp.msg m) ul) (hh.division.sEnd + sc3Num y) y)
    (eVM : ∀ y, SlotAt W Pp.sVM.T u.oVM (Sum.elim (Pp.msg m) ul) (hh.below.sEnd + sc3Num y) y)
    (eVD : ∀ y, SlotAt W Pp.sVD.T u.oVD (Sum.elim (Pp.msg m) ul) (hh.on.sEnd + sc3Num y) y)
    (eF : ∀ y, SlotAt W Pp.sF.T u.oF (Sum.elim (Pp.msg m) ul) (hh.atIndex.sEnd + sc3Num y) y)
    (eK : ∀ y, SlotAt W Pp.sD.T u.oK (Sum.elim (Pp.msg m) ul) (hh.key.sEnd + scdNum (size18 Pp.D) y) y)
    (eH : ∀ y, SlotAt W Pp.sH.T u.oH (Sum.elim (Pp.msg m) ul) (hh.cells.sEnd + sc3Num y) y) :
    SlotsH W (oldOf S gL i) Pp u m
      (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2) ul := by
  have l1 : i.p.scores.toList[0]? = some k1 := by rw [Array.getElem?_toList]; exact hk1
  have l2 : i.p.scores.toList[1]? = some k2 := by rw [Array.getElem?_toList]; exact hk2
  have m1 : hh.scores.toList[0]? = some o1 := by rw [Array.getElem?_toList]; exact ho1
  have m2 : hh.scores.toList[1]? = some o2 := by rw [Array.getElem?_toList]; exact ho2
  have z1 : k1.s0 = o1.1 := nth_of_map (s0_are PA) l1 m1
  have z2 : k2.s0 = o2.1 := nth_of_map (s0_are PA) l2 m2
  have n1 : k1.sc.ends = o1.2.sEnd := nth_of_map (ends_are PA) l1 m1
  have n2 : k2.sc.ends = o2.2.sEnd := nth_of_map (ends_are PA) l2 m2
  have hlT : Pp.D.lT = S.cf.lt := by rw [hD]; exact pub_lT A
  have nF : ∀ {nb : ℕ} (b : Fin nb), sc3Num (b, false) = 2 * b.val := fun b => by simp [sc3Num]
  have nT : ∀ {nb : ℕ} (b : Fin nb), sc3Num (b, true) = 2 * b.val + 1 := fun b => by simp [sc3Num]
  refine ⟨fun j hj => ?_, fun j h3 h6 => ?_, fun j h6 => ?_, fun j => ?_, fun j => ?_, ?_, ?_, fun b => ?_,
    fun b => ⟨?_, ?_⟩, fun b => ⟨?_, ?_⟩, fun b => ⟨?_, ?_⟩, fun b => ⟨?_, ?_⟩, fun b => ⟨?_, ?_⟩,
    fun b => ?_, fun l => ?_, fun b t => ?_, fun b => ⟨?_, ?_⟩⟩
  · have e := rM j
    rw [if_pos (by omega), show j.1 / 3 = 0 by omega, p0, show j.1 % 3 = j.1 by omega] at e
    exact e
  · have e := rM j
    rw [if_pos (by omega), show j.1 / 3 = 1 by omega, p1, show j.1 % 3 = j.1 - 3 by omega] at e
    exact e
  · have e := rM j
    rw [if_neg (by omega), s0, show j.1 - 3 * Pp.npl = j.1 - 6 by omega, ← z1] at e
    exact e
  · have e := rD j
    rw [s1, ← z2] at e
    exact e
  · have e := rE j
    unfold slotEh
    rw [show (oldOf S gL i).d.s5 = hh.five from PA.s5, show (oldOf S gL i).d.sIB = hh.bits from PA.sIB,
      show (oldOf S gL i).d.s5h = hh.two from PA.s5h]
    exact e
  · have e := rV 0
    rw [show (oldOf S gL i).d.sCl = hh.values from PA.sCl]
    exact e
  · have e := rV 1
    rw [show (oldOf S gL i).d.sCl = hh.values from PA.sCl]
    exact e
  · rw [show (oldOf S gL i).x.sM6 = hh.maxima from PA.sM6]
    exact rF b
  · have e := eUM (b, false); rw [nF, e0, ← n1] at e; exact e
  · have e := eUM (b, true); rw [nT, e0, ← n1] at e; exact e
  · have e := eUD (b, false); rw [nF, e1, ← n2] at e; exact e
  · have e := eUD (b, true); rw [nT, e1, ← n2] at e; exact e
  · have e := eE (b, false); rw [nF] at e
    rw [show (oldOf S gL i).d.scE.sEnd = hh.division.sEnd by show i.p.d.scE.ends = _; rw [PA.scE]; rfl]
    exact e
  · have e := eE (b, true); rw [nT] at e
    rw [show (oldOf S gL i).d.scE.sEnd = hh.division.sEnd by show i.p.d.scE.ends = _; rw [PA.scE]; rfl]
    exact e
  · have e := eVM (b, false); rw [nF] at e
    rw [show (oldOf S gL i).d.vpm.sEnd = hh.below.sEnd by show i.p.d.vpm.ends = _; rw [PA.vpm]; rfl]
    exact e
  · have e := eVM (b, true); rw [nT] at e
    rw [show (oldOf S gL i).d.vpm.sEnd = hh.below.sEnd by show i.p.d.vpm.ends = _; rw [PA.vpm]; rfl]
    exact e
  · have e := eVD (b, false); rw [nF] at e
    rw [show (oldOf S gL i).d.vpd.sEnd = hh.on.sEnd by show i.p.d.vpd.ends = _; rw [PA.vpd]; rfl]
    exact e
  · have e := eVD (b, true); rw [nT] at e
    rw [show (oldOf S gL i).d.vpd.sEnd = hh.on.sEnd by show i.p.d.vpd.ends = _; rw [PA.vpd]; rfl]
    exact e
  · have e := eF (b, false); rw [nF] at e
    rw [show (oldOf S gL i).x.scF.sEnd = hh.atIndex.sEnd by show i.p.x.scF.ends = _; rw [PA.scF]; rfl]
    exact e
  · have e := eK (.inl l)
    rw [show (oldOf S gL i).x.sKC = hh.key.sEnd by show i.p.x.scd.ends = _; rw [PA.scd]; rfl]
    exact e
  · have e := eK (.inr (b, t))
    have eL : (size18 Pp.D).Lam = S.Lam := by rw [hD]; rfl
    have et : (size18 Pp.D).lt = S.cf.lt := hlT
    have es : (oldOf S gL i).x.sIb (oldOf S gL i).S b.val t.val =
        hh.key.sEnd + scdNum (size18 Pp.D) (.inr (b, t)) := by
      show i.p.x.scd.ends + (S.Lam + b.val * S.cf.lt + t.val) = _
      rw [PA.scd]
      show hh.key.sEnd + _ = hh.key.sEnd + ((size18 Pp.D).Lam + b.val * (size18 Pp.D).lt + t.val)
      generalize b.val = bv
      generalize t.val = tv
      rw [eL, et]
    rw [es]
    exact e
  · have e := eH (b, false); rw [nF] at e
    rw [show (oldOf S gL i).x.scH.sEnd = hh.cells.sEnd by show i.p.x.scH.ends = _; rw [PA.scH]; rfl]
    exact e
  · have e := eH (b, true); rw [nT] at e
    rw [show (oldOf S gL i).x.scH.sEnd = hh.cells.sEnd by show i.p.x.scH.ends = _; rw [PA.scH]; rfl]
    exact e
end Slots

end K5Law
