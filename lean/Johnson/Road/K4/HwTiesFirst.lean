-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HwTiesFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/HwTies.lean: WHICH ENTRY
OF THE MASK SERVES AS WHICH COEFFICIENT OF A HIDING POLYNOMIAL, AT K4's SEVEN SUMCHECKS, at the
first group's value with its slots and orders laid (`Plan4LF.planF`,
Johnson/Road/K4/ValueSlotsFirst.lean). It pays the record of premises `HwTiesF`
(Johnson/Road/K4/SixLedFirst.lean) at that value.

  `hear_slotsAtF`: the twin of `hear_slotsAt` (Johnson/Road/K4/SlotsTie.lean): where the hearing
    returns in the first group from a ledger with arrays of the right sizes: the same fifteen slot
    numbers are fields of `slotsAt`; the embedding's slot is the formula f7, and the merge's first
    own slot is f7 + 1 (`hear_end_first`, Johnson/Road/K4/HearSlotsEnd.lean).
  `Plan4LF.hw1` … `Plan4LF.hw7`: the value's message at the name wS q (wP, wT, wI, w5, w6, w7) is
    the mask at slotP _ f q, f the formula fS (fP, fT, fI, f5, f6) and, for the merge, f7 + 1.
  `Plan4LF.hmE`: the value's message at the name of the embedding's mask entry is the mask at f7.
  `Plan4LF.hwTiesF_slots`: `HwTiesF` holds at these seven numbers.
  `Plan4LF.firsts_KF`: where `hear` returns, under `LedG` and `MeetsF`: the first own slots of the
    program's seven records are these seven numbers, and the embedding's slot is f7.

NO NEW ARGUMENT: HwTies.lean's proofs at these letters. By hand: f7 + 1; hmE; the embedding's slot.

Limits. `MaskLetters` is a premise (see the limits of Johnson/Road/K4/MaskTiesH.lean); so is room7F:
the merge's own slots, which begin one slot later than in a later group, lie within ns. `firsts_KF`
asks four things more beside `LedG` and `MeetsF`: the ledger in front has arrays of the right sizes
(hF), and the value's three numbers are the hearing's: n0 is the ledger's next free slot in front
(hn0: shown of no value here), nT and nI the plan's two numbers of end values (hnT, hnI). Equations
alone: nothing on what a mask hides, nothing on soundness.
-/
import Johnson.Road.K4.HwTies
import Johnson.Road.K4.ValueSlotsFirst
import Johnson.Road.K4.PlanMapsFirst
import Johnson.Road.K4.SixLedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (Pub HPlan2 Own Heard Reads layout readsOf lamSOf nclOf nEndT normsStart
  downFrom)
open OnBytes.Tie.Pv (slotP)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lDd lF lFe)
open OnBytes.Desc.First.K4 (Par covers engFl hear stackRec hearStack_tape k0 hear_slots
  hear_end_first hear_parts_first)
open OnBytes.Desc.First.P1 (drawnOf levelRec levelIn_heard endP_spec)

section Hearing
variable {hS : Layer.Shape} {D : Dim} [scl : Scl] {pc : List (List String)} {P : Pub} {hp : HPlan2}
  {g : ℕ} {K : Type} [Field K] (ρ : Reading K)

include scl ρ in
/-- **A hearing in the first group holds the value's numbers**, from a ledger with arrays of the
right sizes, under the premises of `dimIs_layerNumbers`. -/
theorem hear_slotsAtF (hy : layout hS pc = .ok P.y) (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS D)
    (hl : hp.lamS = lamSOf P.y) (hn : hp.NCL = nclOf P.y g) {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : OnBytes.PscRun.Sized F)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (hg : (g == 0) = true) {s : Slots4}
    (hs : s = slotsAt D F.next (nEndT P.y)
      (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))) :
    o.H.sW = s.sW ∧ o.H.wpl.sL = s.vS ∧ o.H.sPv = s.sP ∧ o.H.tV.sCl = s.cP0 ∧
      o.H.tV.p.first = s.fP ∧ o.H.tV.sEnd = s.vP ∧
      (∃ tT, o.H.tT = some tT ∧ tT.sCl = s.cT0 ∧ tT.p.first = s.fT ∧ tT.sEnd = s.vT) ∧
      o.K.sA0 = s.vI ∧ o.K.sH1 = s.vI + 1 ∧ o.K.sB0 = s.vI + 1 + (1 + P.y.LamM) ∧
      o.K.sV = s.vI + 1 + (1 + P.y.LamM) + 1 ∧ o.hd.sL = s.v5 ∧
      (∃ hd2, o.hd2 = some hd2 ∧ hd2.sL = s.v6) ∧ o.sVE = s.f7 ∧ o.wo.p.first = s.f7 + 1 := by
  have hc : covers P = true := (hear_parts_first h hg).1
  rw [slotsAt_k4Slots hy hc hrd Z hl hn F.next] at hs
  subst hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hear_slots ρ hF h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, (hear_end_first ρ hF h hg).1,
    (hear_end_first ρ hF h hg).2.1⟩

end Hearing

variable [scl : Scl] {M X : Type} {QF : Plan4LF GE M X}

/-- The squares' sumcheck. -/
theorem Plan4LF.hw1 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (QF.planF.D.lL + 1 + (lDd QF.planF.D + QF.planF.D.lT)) (fun _ => 2) ++
      [pDummy GE 2])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.wS q) = mask (slotP _ QF.toPlan4L.slots.fS q) := by
  have hb : slotP _ QF.planF.fS q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).1
  exact (QF.planF.toPlan4.msg_wS mm q hb).trans (Lm.isM _ hb)

/-- The products' sumcheck. -/
theorem Plan4LF.hw2 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE QF.planF.D.lT (fun _ => 2) ++ [pDummy GE 2])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.wP q) = mask (slotP _ QF.toPlan4L.slots.fP q) := by
  have hb : slotP _ QF.planF.fP q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.1
  exact (QF.planF.toPlan4.msg_wP mm q hb).trans (Lm.isM _ hb)

/-- The terms' sumcheck. -/
theorem Plan4LF.hw3 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE QF.planF.D.lT (fun _ => 2) ++ [pDummy GE 1])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.wT q) = mask (slotP _ QF.toPlan4L.slots.fT q) := by
  have hb : slotP _ QF.planF.fT q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.1
  exact (QF.planF.toPlan4.msg_wT mm q hb).trans (Lm.isM _ hb)

/-- The batched sumcheck. -/
theorem Plan4LF.hw4 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (kS QF.planF.D) (fun _ => 2) ++ [pDummy GE 2])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.wI q) = mask (slotP _ QF.toPlan4L.slots.fI q) := by
  have hb : slotP _ QF.planF.fI q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.2.1
  exact (QF.planF.toPlan4.msg_wI mm q hb).trans (Lm.isM _ hb)

/-- The gated layer. -/
theorem Plan4LF.hw5 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (QF.planF.D.lL + lF QF.planF.D + QF.planF.D.lT) (fun _ => 2) ++
      [pDummy GE 2])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.w5 q) = mask (slotP _ QF.toPlan4L.slots.f5 q) := by
  have hb : slotP _ QF.planF.f5 q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.2.2.1
  exact (QF.planF.toPlan4.msg_w5 mm q hb).trans (Lm.isM _ hb)

/-- The routed gated layer. -/
theorem Plan4LF.hw6 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (QF.planF.D.lL - 1 + (lFe QF.planF.D + QF.planF.D.lT)) (fun _ => 2) ++
      [pDummy GE 2])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.w6 q) = mask (slotP _ QF.toPlan4L.slots.f6 q) := by
  have hb : slotP _ QF.planF.f6 q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.2.2.2
  exact (QF.planF.toPlan4.msg_w6 mm q hb).trans (Lm.isM _ hb)

/-- The merge: its first own slot is the formula f7 + 1. -/
theorem Plan4LF.hw7 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (room7F : QF.toPlan4L.slots.f7 + 1 + 1 + (2 * QF.planF.kW + 1) ≤ QF.ns)
    (q : PIdx (ldPartFmt GE QF.planF.kW (fun _ => 2) ++ [pDummy GE 1])) :
    QF.planF.fullF.msg mm (QF.planF.fullF.w7 q) =
      mask (slotP _ (QF.toPlan4L.slots.f7 + 1) q) := by
  have hb : slotP _ QF.planF.f7 q ≤ QF.planF.ns :=
    slot_within q (fmt_sum_ld _ _) room7F
  exact (QF.planF.toPlan4.msg_w7 mm q hb).trans (Lm.isM _ hb)

/-- The embedding's mask entry lies at the formula f7. -/
theorem Plan4LF.hmE (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI) :
    QF.planF.fullF.msg mm QF.planF.fullF.mkE = mask QF.toPlan4L.slots.f7 :=
  (QF.planF.toPlan4.msg_sl mm (n := QF.toPlan4L.slots.f7) Lm.room).trans (Lm.isM _ Lm.room)

/-- **`HwTiesF` holds at the formulas' first slots**; the merge's is f7 + 1. -/
theorem Plan4LF.hwTiesF_slots (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI)
    (room7F : QF.toPlan4L.slots.f7 + 1 + 1 + (2 * QF.planF.kW + 1) ≤ QF.ns) :
    HwTiesF QF.planF.fullF (QF.planF.fullF.msg mm) mask QF.toPlan4L.slots.fS
      QF.toPlan4L.slots.fP QF.toPlan4L.slots.fT QF.toPlan4L.slots.fI QF.toPlan4L.slots.f5
      QF.toPlan4L.slots.f6 (QF.toPlan4L.slots.f7 + 1) where
  hw1 := Plan4LF.hw1 mm mask Lm
  hw2 := Plan4LF.hw2 mm mask Lm
  hw3 := Plan4LF.hw3 mm mask Lm
  hw4 := Plan4LF.hw4 mm mask Lm
  hw5 := Plan4LF.hw5 mm mask Lm
  hw6 := Plan4LF.hw6 mm mask Lm
  hw7 := Plan4LF.hw7 mm mask Lm room7F

variable {par : Par} {hS : Layer.Shape} {pcl : List (List String)}

/-- **The seven records' first own slots are the formulas'**, the merge's f7 + 1, and the
embedding's slot is f7. Pp: the place's public record with the run's tokens. -/
theorem Plan4LF.firsts_KF (A : QF.planF.MeetsF par hS pcl) {tk : Array Nat} {Pp : Pub}
    (hPp : Pp = { par.P with tokv := tk }) {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u u5 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} (hF : PscRun.Sized F)
    (h : hear engFl Pp par.hp par.g fo F t0 = some (o, G, u))
    (Ld : LedG Pp par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (hn0 : QF.n0 = F.next) (hnT : QF.nT = nEndT par.P.y)
    (hnI : QF.nI =
      2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))) :
    (levelRec Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 par.g)).drop 1)).toArray H1.PV).2
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 par.g)).drop 1)).toArray H1.PV).1
        (orderDefault Pp.rd.muV) F4 ((ksOf Pp par.hp).tc1 (t0.drop (k0 par.g)))).first =
        QF.toPlan4L.slots.fS ∧
      H1.tV.p.first = QF.toPlan4L.slots.fP ∧ tT.p.first = QF.toPlan4L.slots.fT ∧
      (stackRec o.v o.H par.hp.lamS G2 ((ksOf Pp par.hp).tc4 (t0.drop (k0 par.g)))).first =
        QF.toPlan4L.slots.fI ∧
      (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
        (orderRange Pp.rd.muH) G3 ((ksOf Pp par.hp).tc5 (t0.drop (k0 par.g)))).first =
        QF.toPlan4L.slots.f5 ∧
      (levelRec Pp.rd.muH2
        ((drawnOf ((((ksOf Pp par.hp).tc5 (t0.drop (k0 par.g))).drop
          (Pp.rd.muH + 3)).drop 1)).toArray ++ downFrom o.K.rs Pp.y.lfe ++ tT.r)
        (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp par.hp).tc5 (t0.drop (k0 par.g))).drop
            (Pp.rd.muH + 3)).drop 1)).toArray)
        (orderRange Pp.rd.muH2) G3' ((ksOf Pp par.hp).tc6 (t0.drop (k0 par.g)))).first =
        QF.toPlan4L.slots.f6 ∧
      o.wo.p.first = QF.toPlan4L.slots.f7 + 1 ∧ o.sVE = QF.toPlan4L.slots.f7 := by
  subst hPp
  have hsl : QF.toPlan4L.slots = slotsAt QF.planF.D F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))) := by
    show slotsAt QF.D QF.n0 QF.nT QF.nI = _
    rw [hn0, hnT, hnI]
    rfl
  obtain ⟨_, a2, _, _, a5, _, ⟨tT', e7, _, a7, _⟩, a8, _, _, _, a12, ⟨hd2', e13, a13⟩, aE, a14⟩ :=
    hear_slotsAtF Reading.gl (P := { par.P with tokv := tk }) A.hy A.hrd A.Z A.hl A.hn hF h A.hg
      hsl
  have Xd := A.dimIs
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.hrd
  have xlt : QF.planF.D.lT = par.P.y.h.lt := Xd.lt
  have xlNI : QF.planF.D.lL + 1 = par.P.rd.lNI := Xd.lNI
  have xlPd : lDd QF.planF.D = par.P.y.lPd := Xd.lPd
  have xll : QF.planF.D.lL = par.P.y.h.ll := Xd.ll
  have xlPf : lF QF.planF.D = par.P.y.lPf := Xd.lPf
  have xlfe : lFe QF.planF.D = par.P.y.lfe := Xd.lfe
  have xk : kS QF.planF.D = par.hp.lamS := (kS_eq QF.planF.D).trans Xd.lamS
  obtain ⟨v1, c1⟩ := Ld.c1
  obtain ⟨v5, c5⟩ := Ld.c5
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, f1, _, l1, _⟩ := levelIn_heard c1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, f5, _, l5, _⟩ := levelIn_heard c5
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, f6, _, l6, _⟩ := levelIn_heard Ld.c6
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hsA0, _⟩ := hearStack_tape Ld.c4
  have eT : tT'.p.first = tT.p.first := by
    rw [Ld.kTT] at e7
    rw [← Option.some.inj e7]
  have eH : hd2' = hd2 := by
    rw [Ld.eHd2] at e13
    exact (Option.some.inj e13).symm
  have v1e : QF.toPlan4L.slots.vS = QF.toPlan4L.slots.fS +
      (1 + 2 * (QF.planF.D.lL + 1 + (lDd QF.planF.D + QF.planF.D.lT)) + 2) := rfl
  have v4e : QF.toPlan4L.slots.vI = QF.toPlan4L.slots.fI + (1 + 2 * kS QF.planF.D + 2) := rfl
  have v5e : QF.toPlan4L.slots.v5 = QF.toPlan4L.slots.f5 +
      (1 + 2 * (QF.planF.D.lL + lF QF.planF.D + QF.planF.D.lT) + 2) := rfl
  have v6e : QF.toPlan4L.slots.v6 = QF.toPlan4L.slots.f6 +
      (1 + 2 * (QF.planF.D.lL - 1 + (lFe QF.planF.D + QF.planF.D.lT)) + 2) := rfl
  rw [Ld.kWpl] at a2
  rw [Ld.kTV] at a5
  rw [eH] at a13
  have l1' : H1.wpl.sL = F4.next + 1 + 2 * par.P.rd.muV + 2 := l1
  have h4' : o.K.sA0 = G2.next + 1 + 2 * par.hp.lamS + 2 := hsA0
  have l5' : o.hd.sL = G3.next + 1 + 2 * par.P.rd.muH + 2 := l5
  have l6' : hd2.sL = G3'.next + 1 + 2 * par.P.rd.muH2 + 2 := l6
  refine ⟨f1.trans ?_, a5, eT ▸ a7, ((endP_spec _ _ _).2.2.2.2.2.2).trans ?_, f5.trans ?_,
    f6.trans ?_, a14, aE⟩
  · omega
  · show G2.next = QF.toPlan4L.slots.fI
    omega
  · omega
  · omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hear_slotsAtF
#print axioms OnBytes.Road.K4.Plan4LF.hmE
#print axioms OnBytes.Road.K4.Plan4LF.hwTiesF_slots
#print axioms OnBytes.Road.K4.Plan4LF.firsts_KF
