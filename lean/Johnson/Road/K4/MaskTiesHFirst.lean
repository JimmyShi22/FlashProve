-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MaskTiesHFirst.lean: THE FIRST GROUP's TWIN OF `Plan4L.hm_of`
(Johnson/Road/K4/MaskTiesH.lean) AND OF `Plan4L.hkI_of` (Johnson/Road/K4/KIncTie.lean): THE ENTRY OF
THE VALUE's MESSAGE UNDER A TYPED NAME OF A MASK ENTRY IS THE MASK's ENTRY AT K4's SLOT, at the
first group's value with its slots and orders laid (`Plan4LF.planF`,
Johnson/Road/K4/ValueSlotsFirst.lean). Two statements with their proofs.

  `Plan4LF.hm_ofF`: SEVEN ties, where `hear` returns, under `LedG` and `MeetsF`: the six of
    `Plan4L.hm_of` (the premises hm of `hincH1F` … `hincH7F`, Johnson/Road/K4/IncsHeardFirst.lean)
    and the seventh, hmE: the entry under the name mkE is the mask's at the embedding's slot.
  `Plan4LF.hkI_ofF`: the sum of the lookup's end form's coefficients over the value's names is the
    sum over the mask's slots below ns + 1.

NO NEW ARGUMENT: the two files' proofs at these letters, over `hear_slotsAtF` and `Plan4LF.hmE`
(Johnson/Road/K4/HwTiesFirst.lean).

Limits. `MaskLetters` is a premise (see MaskTiesH.lean's limits); so are, in the first, that the
ledger in front has arrays of the right sizes (hF) and LamM = ne, and, in the second, that the
value's letter kIncS at x is `kIncAt fo F`. Equations alone: nothing on what a mask hides, nothing
on soundness.
-/
import Johnson.Road.K4.HwTiesFirst
import Johnson.Road.K4.KIncTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Finset
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (Par engFl hear)

variable [scl : Scl] {M X : Type} {QF : Plan4LF GE M X} {par : Par} {hS : Layer.Shape}
  {pcl : List (List String)}

/-- **The seven ties.** -/
theorem Plan4LF.hm_ofF (A : QF.planF.MeetsF par hS pcl) {tk : Array Nat} {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u u5 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} (hF : PscRun.Sized F)
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (Ld : LedG { par.P with tokv := tk } par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2
      G3 G3' G4 G5 u5)
    (hLam : par.P.y.LamM = QF.planF.D.ne) (mm : M) (mask : ℕ → GE)
    (Lm : MaskLetters QF.toPlan4L mm mask F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0)))) :
    (∀ (i : Fin QF.planF.fullF.D.nNu) (s : Fin 9),
      QF.planF.fullF.msg mm (QF.planF.fullF.nr.sq.mkS i s) =
        mask (H1.sW + 9 * i.val + s.val)) ∧
    QF.planF.fullF.msg mm QF.planF.fullF.nr.rows.rJ = mask H1.tV.sCl ∧
    QF.planF.fullF.msg mm QF.planF.fullF.rT = mask tT.sCl ∧
    QF.planF.fullF.msg mm (QF.planF.fullF.cI (.inl (aH1 QF.planF.fullF.D))) = mask o.K.sH1 ∧
    (∀ i : Fin QF.planF.fullF.D.ne,
      QF.planF.fullF.msg mm (QF.planF.fullF.cI (.inl (aH2 QF.planF.fullF.D i))) =
        mask (o.K.sH1 + 1 + i.val)) ∧
    (∀ a : Fin QF.planF.fullF.nW,
      QF.planF.fullF.msg mm (QF.planF.fullF.wp0.wt.nm a) = mask (o.K.sV + a.val)) ∧
    QF.planF.fullF.msg mm QF.planF.fullF.mkE = mask o.sVE := by
  have hsl : QF.toPlan4L.slots = slotsAt QF.planF.D F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))) := by
    show slotsAt QF.D QF.n0 QF.nT QF.nI = _
    rw [Lm.n0, Lm.nT, Lm.nI]
    rfl
  obtain ⟨a1, _, _, a4, _, _, ⟨tT', e7, a7, _, _⟩, _, a9, _, a11, _, _, aE, _⟩ :=
    hear_slotsAtF Reading.gl (P := { par.P with tokv := tk }) A.hy A.hrd A.Z A.hl A.hn hF h A.hg
      hsl
  obtain ⟨r1, r2, r3, r4⟩ := slotsAt_within QF.planF.D F.next (nEndT par.P.y)
    (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0)))
  rw [← hsl] at r1 r2 r3 r4
  have room := Lm.room
  have hW : QF.planF.nW = par.hp.NCL - (if (par.g == 0) = true then 1 else 0) :=
    OnBytes.Tie.Pv.Lay.At.nW_eq QF.planF.fullF.toFullPar _ A.dimIs
  have eT : tT'.sCl = tT.sCl := by
    rw [Ld.kTT] at e7
    rw [← Option.some.inj e7]
  refine ⟨fun i s => ?_, ?_, ?_, ?_, fun i => ?_, fun a => ?_, ?_⟩
  · have hi : i.val < QF.planF.D.nNu := i.isLt
    have hs := s.isLt
    have hb : QF.planF.sW + 9 * i + s ≤ QF.planF.ns := by
      show QF.toPlan4L.slots.sW + 9 * i.val + s.val ≤ QF.ns
      omega
    refine (QF.planF.toPlan4.msg_mkS mm i s hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    show QF.toPlan4L.slots.sW + 9 * i.val + s.val = _
    rw [← a1, Ld.kSW]
  · have hb : QF.planF.cP0 ≤ QF.planF.ns := r2.trans room
    refine (QF.planF.toPlan4.msg_rP mm hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    show QF.toPlan4L.slots.cP0 = _
    rw [← a4, Ld.kTV]
  · have hb : QF.planF.cT0 ≤ QF.planF.ns := r3.trans room
    refine (QF.planF.toPlan4.msg_rT mm hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    show QF.toPlan4L.slots.cT0 = _
    rw [← a7, eT]
  · have e : QF.planF.numI (.inl (aH1 QF.planF.D)) = 1 := by
      show QF.numI _ = 1
      rw [Lm.numI]
      rfl
    have hb : QF.planF.vI + QF.planF.numI (.inl (aH1 QF.planF.D)) ≤ QF.planF.ns := by
      rw [e]
      show QF.toPlan4L.slots.vI + 1 ≤ QF.ns
      omega
    refine (QF.planF.toPlan4.msg_cI mm _ hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    rw [e, a9]
    rfl
  · have hi : i.val < QF.planF.D.ne := i.isLt
    have e : QF.planF.numI (.inl (aH2 QF.planF.D i)) = 2 + i.val := by
      show QF.numI _ = _
      rw [Lm.numI]
      rfl
    have hb : QF.planF.vI + QF.planF.numI (.inl (aH2 QF.planF.D i)) ≤ QF.planF.ns := by
      rw [e]
      show QF.toPlan4L.slots.vI + (2 + i.val) ≤ QF.ns
      omega
    refine (QF.planF.toPlan4.msg_cI mm _ hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    rw [e, a9]
    show QF.toPlan4L.slots.vI + (2 + i.val) = QF.toPlan4L.slots.vI + 1 + 1 + i.val
    omega
  · have ha : a.val < QF.planF.nW := a.isLt
    have e : QF.planF.numI (.inr (.inr (QF.planF.num a))) =
        2 + (1 + QF.planF.D.ne) + a.val := by
      show QF.numI _ = _
      rw [Lm.numI]
      show 2 + (1 + QF.D.ne) + (QF.num.symm (QF.num a)).val = _
      rw [Equiv.symm_apply_apply]
      rfl
    have hb : QF.planF.vI + QF.planF.numI (.inr (.inr (QF.planF.num a))) ≤ QF.planF.ns := by
      rw [e]
      show QF.toPlan4L.slots.vI + (2 + (1 + QF.planF.D.ne) + a.val) ≤ QF.ns
      omega
    refine (QF.planF.toPlan4.msg_cI mm _ hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    rw [e, a11]
    show QF.toPlan4L.slots.vI + (2 + (1 + QF.planF.D.ne) + a.val) =
      QF.toPlan4L.slots.vI + 1 + (1 + par.P.y.LamM) + 1 + a.val
    omega
  · rw [aE]
    exact Plan4LF.hmE mm mask Lm

/-- **The premise hkI.** -/
theorem Plan4LF.hkI_ofF (x : X) (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QF.toPlan4L mm mask n0 nT nI) {fo : Forest.Heard} {F : Fork}
    (hS : ∀ s, QF.planF.kIncS x s = kIncAt fo F s) :
    ∑ j, QF.planF.fullF.kInc x j * QF.planF.fullF.msg mm j =
      ∑ s : Fin (QF.ns + 1), kIncAt fo F s * mask s := by
  have e : ∑ j : QF.planF.J, QF.planF.toPlan4.kInc x j * QF.planF.toPlan4.msg mm j =
      ∑ s : Fin (QF.planF.ns + 1), QF.planF.kIncS x s * QF.planF.maskAt mm s := by
    simp only [Fintype.sum_sum_type, Plan4.kInc, Plan4.msg, zero_mul, sum_const_zero, zero_add,
      add_zero]
  refine e.trans (Finset.sum_congr rfl fun s _ => ?_)
  rw [hS]
  exact congrArg _ (Lm.isM _ (Nat.lt_succ_iff.mp s.isLt))

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.hm_ofF
#print axioms OnBytes.Road.K4.Plan4LF.hkI_ofF
