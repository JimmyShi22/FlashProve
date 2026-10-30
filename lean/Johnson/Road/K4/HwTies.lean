-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HwTies.lean: WHICH ENTRY OF THE MASK SERVES AS WHICH COEFFICIENT OF A HIDING
POLYNOMIAL, AT K4's SEVEN SUMCHECKS: the value's message, at the typed name of a coefficient, is the
mask at the slot that the program's record gives that coefficient. At the value with its slots and
orders laid (`Plan4L.plan`, Johnson/Road/K4/ValueSlots.lean), in a group that is not the first.
Beside Johnson/Road/K4/MaskTiesH.lean.

  `slot_within`: a coefficient's slot lies below f + 1 + the sum of the degrees (by
    `slotP_bounds`, Johnson/Top/H0/K11Caller/AtSlots.lean). `fmt_sum_ld`: that sum is twice the
    number of variables and the further degree. `slots_firsts`: six bounds between the formulas.
  `Plan4L.hw1` … `Plan4L.hw7`: for every index q of a coefficient of the sumcheck: the value's
    message at the name wS q (wP, wT, wI, w5, w6, w7) is the mask at slotP _ f q, f the formula fS
    (fP, fT, fI, f5, f6, f7). Under `MaskLetters` alone; hw7 also under room7.
  `HwTies V m mask f1 … f7`: the seven, said at the stages' typed sumchecks: m (par.wAt q) =
    mask (slotP par.fmt f q). `Plan4L.hwTies_slots`: they hold at the formulas.
  `Plan4L.firsts_K`: where `hear` returns, under `Led7` and `Meets`: the first own slots of the
    program's seven records are these seven formulas.

HOW. `Plan4.msg_wS` … `msg_w7` (Johnson/Road/K4/ValueMasks.lean) say at which number the value's
message reads maskAt. Of the records' first slots three stand in `hear_slotsAt`
(Johnson/Road/K4/SlotsTie.lean); four come from the slot of the first end value, which lies
1 + 2 k + 2 behind the first own slot (`levelIn_heard`, `hearStack_tape`).

Limits. `MaskLetters` is a premise (see MaskTiesH.lean's limits); so is room7: the merge's own slots
lie within ns. Equations alone: nothing on what a mask hides, nothing on soundness.
-/
import Johnson.Road.K4.MaskTiesH
import Johnson.Top.H0.K11Caller.AtSlots
import Cb.Pv.Lay.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT normsStart downFrom)
open OnBytes.Tie.Pv (slotP)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lDd lF lFe)
open OnBytes.Desc.First.K4 (Par engFl hear stackRec hearStack_tape)
open OnBytes.Desc.First.P1 (drawnOf levelRec levelIn_heard endP_spec)

/-- A coefficient's slot lies within the sumcheck's own slots. -/
theorem slot_within {l : List (PFmt GE)} {s c ns : ℕ} (q : PIdx l)
    (hs : (l.map PFmt.n).sum = c) (h : s + 1 + c ≤ ns) : slotP l s q ≤ ns := by
  have b := (VerifiableInference.Desc.First.K11Caller.slotP_bounds l s q).2
  omega

/-- The sum of the degrees. -/
theorem fmt_sum_ld (k dy : ℕ) :
    ((ldPartFmt GE k (fun _ => 2) ++ [pDummy GE dy]).map PFmt.n).sum = 2 * k + dy := by
  rw [fmt_rep, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate]
  show k • 2 + (dy + 0) = _
  simp only [smul_eq_mul]
  omega

/-- Six bounds between the formulas. -/
theorem slots_firsts (D : Dim) (n0 nT nI ns : ℕ) (h : (slotsAt D n0 nT nI).f7 ≤ ns) :
    (slotsAt D n0 nT nI).fS + 1 + (2 * (D.lL + 1 + (lDd D + D.lT)) + 2) ≤ ns ∧
      (slotsAt D n0 nT nI).fP + 1 + (2 * D.lT + 2) ≤ ns ∧
      (slotsAt D n0 nT nI).fT + 1 + (2 * D.lT + 1) ≤ ns ∧
      (slotsAt D n0 nT nI).fI + 1 + (2 * kS D + 2) ≤ ns ∧
      (slotsAt D n0 nT nI).f5 + 1 + (2 * (D.lL + lF D + D.lT) + 2) ≤ ns ∧
      (slotsAt D n0 nT nI).f6 + 1 + (2 * (D.lL - 1 + (lFe D + D.lT)) + 2) ≤ ns := by
  simp only [slotsAt] at h ⊢
  omega

variable [scl : Scl] {M X : Type} {QL : Plan4L GE M X}

/-- The squares' sumcheck. -/
theorem Plan4L.hw1 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (QL.plan.D.lL + 1 + (lDd QL.plan.D + QL.plan.D.lT)) (fun _ => 2) ++
      [pDummy GE 2])) :
    QL.plan.full.msg mm (QL.plan.full.wS q) = mask (slotP _ QL.slots.fS q) := by
  have hb : slotP _ QL.plan.fS q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).1
  exact (QL.plan.msg_wS mm q hb).trans (Lm.isM _ hb)

/-- The products' sumcheck. -/
theorem Plan4L.hw2 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE QL.plan.D.lT (fun _ => 2) ++ [pDummy GE 2])) :
    QL.plan.full.msg mm (QL.plan.full.wP q) = mask (slotP _ QL.slots.fP q) := by
  have hb : slotP _ QL.plan.fP q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.1
  exact (QL.plan.msg_wP mm q hb).trans (Lm.isM _ hb)

/-- The terms' sumcheck. -/
theorem Plan4L.hw3 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE QL.plan.D.lT (fun _ => 2) ++ [pDummy GE 1])) :
    QL.plan.full.msg mm (QL.plan.full.wT q) = mask (slotP _ QL.slots.fT q) := by
  have hb : slotP _ QL.plan.fT q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.1
  exact (QL.plan.msg_wT mm q hb).trans (Lm.isM _ hb)

/-- The batched sumcheck. -/
theorem Plan4L.hw4 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (kS QL.plan.D) (fun _ => 2) ++ [pDummy GE 2])) :
    QL.plan.full.msg mm (QL.plan.full.wI q) = mask (slotP _ QL.slots.fI q) := by
  have hb : slotP _ QL.plan.fI q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.2.1
  exact (QL.plan.msg_wI mm q hb).trans (Lm.isM _ hb)

/-- The gated layer. -/
theorem Plan4L.hw5 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (QL.plan.D.lL + lF QL.plan.D + QL.plan.D.lT) (fun _ => 2) ++
      [pDummy GE 2])) :
    QL.plan.full.msg mm (QL.plan.full.w5 q) = mask (slotP _ QL.slots.f5 q) := by
  have hb : slotP _ QL.plan.f5 q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.2.2.1
  exact (QL.plan.msg_w5 mm q hb).trans (Lm.isM _ hb)

/-- The routed gated layer. -/
theorem Plan4L.hw6 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (q : PIdx (ldPartFmt GE (QL.plan.D.lL - 1 + (lFe QL.plan.D + QL.plan.D.lT)) (fun _ => 2) ++
      [pDummy GE 2])) :
    QL.plan.full.msg mm (QL.plan.full.w6 q) = mask (slotP _ QL.slots.f6 q) := by
  have hb : slotP _ QL.plan.f6 q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) (slots_firsts _ _ _ _ _ Lm.room).2.2.2.2.2
  exact (QL.plan.msg_w6 mm q hb).trans (Lm.isM _ hb)

/-- The merge. -/
theorem Plan4L.hw7 (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (room7 : QL.slots.f7 + 1 + (2 * QL.plan.kW + 1) ≤ QL.ns)
    (q : PIdx (ldPartFmt GE QL.plan.kW (fun _ => 2) ++ [pDummy GE 1])) :
    QL.plan.full.msg mm (QL.plan.full.w7 q) = mask (slotP _ QL.slots.f7 q) := by
  have hb : slotP _ QL.plan.f7 q ≤ QL.plan.ns :=
    slot_within q (fmt_sum_ld _ _) room7
  exact (QL.plan.msg_w7 mm q hb).trans (Lm.isM _ hb)

/-- The seven equations, at the stages' typed sumchecks. -/
structure HwTies (V : FullPar GE M X) (m : V.J → GE) (mask : ℕ → GE)
    (f1 f2 f3 f4 f5 f6 f7 : ℕ) : Prop where
  hw1 : ∀ q, m (V.nr.sq.R.L.toSum.T.par.wAt q) = mask (slotP V.nr.sq.R.L.toSum.T.par.fmt f1 q)
  hw2 : ∀ q, m (V.own.toOwn.tail.s2.L.T.par.wAt q) =
    mask (slotP V.own.toOwn.tail.s2.L.T.par.fmt f2 q)
  hw3 : ∀ q, m (V.own.toOwn.tail.s3.L.T.par.wAt q) =
    mask (slotP V.own.toOwn.tail.s3.L.T.par.fmt f3 q)
  hw4 : ∀ q, m (V.ip.inn.toSum.T.par.wAt q) = mask (slotP V.ip.inn.toSum.T.par.fmt f4 q)
  hw5 : ∀ q, m (V.fp.gp.toSum.T.par.wAt q) = mask (slotP V.fp.gp.toSum.T.par.fmt f5 q)
  hw6 : ∀ q, m (V.fp.rt.L.toSum.T.par.wAt q) = mask (slotP V.fp.rt.L.toSum.T.par.fmt f6 q)
  hw7 : ∀ q, m (V.wp0.wt.L.toSum.T.par.wAt q) = mask (slotP V.wp0.wt.L.toSum.T.par.fmt f7 q)

/-- **They hold at the formulas' first slots.** -/
theorem Plan4L.hwTies_slots (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI)
    (room7 : QL.slots.f7 + 1 + (2 * QL.plan.kW + 1) ≤ QL.ns) :
    HwTies QL.plan.full (QL.plan.full.msg mm) mask QL.slots.fS QL.slots.fP QL.slots.fT
      QL.slots.fI QL.slots.f5 QL.slots.f6 QL.slots.f7 where
  hw1 := Plan4L.hw1 mm mask Lm
  hw2 := Plan4L.hw2 mm mask Lm
  hw3 := Plan4L.hw3 mm mask Lm
  hw4 := Plan4L.hw4 mm mask Lm
  hw5 := Plan4L.hw5 mm mask Lm
  hw6 := Plan4L.hw6 mm mask Lm
  hw7 := Plan4L.hw7 mm mask Lm room7

variable {par : Par} {hS : Layer.Shape} {pcl : List (List String)}

/-- **The seven records' first own slots are the formulas'.** Pp: the place's public record with
the run's tokens. -/
theorem Plan4L.firsts_K (A : QL.plan.Meets par hS pcl) {tk : Array Nat} {Pp : Pub}
    (hPp : Pp = { par.P with tokv := tk }) {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} (hF : PscRun.Sized F)
    (h : hear engFl Pp par.hp par.g fo F t0 = some (o, G, u))
    (Ld : Led7 Pp par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hn0 : QL.n0 = F.next) (hnT : QL.nT = nEndT par.P.y)
    (hnI : QL.nI =
      2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))) :
    (levelRec Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
        (orderDefault Pp.rd.muV) F4 ((ksOf Pp par.hp).tc1 (t0.drop 1))).first = QL.slots.fS ∧
      H1.tV.p.first = QL.slots.fP ∧ tT.p.first = QL.slots.fT ∧
      (stackRec o.v o.H par.hp.lamS G2 ((ksOf Pp par.hp).tc4 (t0.drop 1))).first =
        QL.slots.fI ∧
      (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
        (orderRange Pp.rd.muH) G3 ((ksOf Pp par.hp).tc5 (t0.drop 1))).first = QL.slots.f5 ∧
      (levelRec Pp.rd.muH2
        ((drawnOf ((((ksOf Pp par.hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r)
        (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp par.hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray)
        (orderRange Pp.rd.muH2) G3' ((ksOf Pp par.hp).tc6 (t0.drop 1))).first = QL.slots.f6 ∧
      o.wo.p.first = QL.slots.f7 := by
  subst hPp
  have hsl : QL.slots = slotsAt QL.plan.D F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))) := by
    show slotsAt QL.D QL.n0 QL.nT QL.nI = _
    rw [hn0, hnT, hnI]
    rfl
  obtain ⟨_, a2, _, _, a5, _, ⟨tT', e7, _, a7, _⟩, a8, _, _, _, a12, ⟨hd2', e13, a13⟩, a14⟩ :=
    hear_slotsAt Reading.gl (P := { par.P with tokv := tk }) A.hy A.hrd A.Z A.hl A.hn hF h A.hg
      hsl
  have Xd := A.dimIs
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.hrd
  have xlt : QL.plan.D.lT = par.P.y.h.lt := Xd.lt
  have xlNI : QL.plan.D.lL + 1 = par.P.rd.lNI := Xd.lNI
  have xlPd : lDd QL.plan.D = par.P.y.lPd := Xd.lPd
  have xll : QL.plan.D.lL = par.P.y.h.ll := Xd.ll
  have xlPf : lF QL.plan.D = par.P.y.lPf := Xd.lPf
  have xlfe : lFe QL.plan.D = par.P.y.lfe := Xd.lfe
  have xk : kS QL.plan.D = par.hp.lamS := (kS_eq QL.plan.D).trans Xd.lamS
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
  have v1e : QL.slots.vS =
      QL.slots.fS + (1 + 2 * (QL.plan.D.lL + 1 + (lDd QL.plan.D + QL.plan.D.lT)) + 2) := rfl
  have v4e : QL.slots.vI = QL.slots.fI + (1 + 2 * kS QL.plan.D + 2) := rfl
  have v5e : QL.slots.v5 =
      QL.slots.f5 + (1 + 2 * (QL.plan.D.lL + lF QL.plan.D + QL.plan.D.lT) + 2) := rfl
  have v6e : QL.slots.v6 =
      QL.slots.f6 + (1 + 2 * (QL.plan.D.lL - 1 + (lFe QL.plan.D + QL.plan.D.lT)) + 2) := rfl
  rw [Ld.kWpl] at a2
  rw [Ld.kTV] at a5
  rw [eH] at a13
  have l1' : H1.wpl.sL = F4.next + 1 + 2 * par.P.rd.muV + 2 := l1
  have h4' : o.K.sA0 = G2.next + 1 + 2 * par.hp.lamS + 2 := hsA0
  have l5' : o.hd.sL = G3.next + 1 + 2 * par.P.rd.muH + 2 := l5
  have l6' : hd2.sL = G3'.next + 1 + 2 * par.P.rd.muH2 + 2 := l6
  refine ⟨f1.trans ?_, a5, eT ▸ a7, ((endP_spec _ _ _).2.2.2.2.2.2).trans ?_, f5.trans ?_,
    f6.trans ?_, a14⟩
  · omega
  · show G2.next = QL.slots.fI
    omega
  · omega
  · omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.hwTies_slots
#print axioms OnBytes.Road.K4.Plan4L.firsts_K
