-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MaskTiesH.lean: THE SIX TIES hm OF `hincH1` … `hincH7`
(Johnson/Road/K4/IncsHeard.lean): the value's message, at the names of the mask entries under the
slots that K4's six start forms name, is the mask at these slots. At the value with its slots and
orders laid (`Plan4L.plan`, Johnson/Road/K4/ValueSlots.lean), in a group that is not the first. A
record, a lemma on the formulas and one theorem.

  `MaskLetters QL mm mask n0 nT nI`: SIX CHOICES OF THE VALUE's LETTERS, premises all: the first
    free slot in front is n0; the numbers of the terms' and of the batched sumcheck's end values are
    nT and nI; the batched sumcheck's end values are numbered by `num4` (Johnson/Road/K4/Num4.lean);
    the value's letter maskAt at mm is the mask, up to ns; the slots of K4's own rounds in front of
    the merge's lie within ns.
  `slotsAt_within`: four bounds between the formulas of `slotsAt`.
  `Plan4L.withMask`, `maskLetters_withMask`, `room7_withMask`, `meets_withMask`: the six choices can
    be made together: at any value with these six letters laid anew, `MaskLetters` holds, at every
    message at once; the merge's own slots lie within ns; and `Meets` goes over from the value
    one began with. n0 stays to be chosen as the ledger's next slot in front.
  `Plan4L.hm_of`: the six ties, where `hear` returns, under `Led7` and `Meets`.

HOW. `Plan4.msg_mkS`, `msg_rP`, `msg_rT`, `msg_cI` (Johnson/Road/K4/ValueMasks.lean) say at which
number the value's message reads maskAt; `hear_slotsAt` (Johnson/Road/K4/SlotsTie.lean) says that
the hearing's slots are the formulas' at n0 := the ledger's next slot in front.

Limits. `MaskLetters` is a premise: n0 is one number for the value, so it can hold only where the
ledger's next slot in front of K4 is that number. Equations alone: nothing on what a mask hides,
nothing on soundness.
-/
import Johnson.Road.K4.IncsHeard
import Johnson.Road.K4.ValueMasks
import Johnson.Road.K4.SlotsTie
import Johnson.Road.K4.ClaimsPaid
import Johnson.Road.K4.Num4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par engFl hear)

variable [scl : Scl] {M X : Type}

/-- Six choices of the value's letters. -/
structure MaskLetters (QL : Plan4L GE M X) (mm : M) (mask : ℕ → GE) (n0 nT nI : ℕ) : Prop where
  n0 : QL.n0 = n0
  nT : QL.nT = nT
  nI : QL.nI = nI
  numI : QL.numI = num4 QL.D QL.num
  isM : ∀ n, n ≤ QL.ns → QL.maskAt mm n = mask n
  room : QL.slots.f7 ≤ QL.ns

omit scl in
/-- Four bounds between the formulas. -/
theorem slotsAt_within (D : Dim) (n0 nT nI : ℕ) :
    (slotsAt D n0 nT nI).sW + 9 * D.nNu ≤ (slotsAt D n0 nT nI).f7 ∧
      (slotsAt D n0 nT nI).cP0 ≤ (slotsAt D n0 nT nI).f7 ∧
      (slotsAt D n0 nT nI).cT0 ≤ (slotsAt D n0 nT nI).f7 ∧
      (slotsAt D n0 nT nI).vI + nI ≤ (slotsAt D n0 nT nI).f7 := by
  simp only [slotsAt]
  omega

/-- The letters laid so: any value's other letters; n0, nT, nI as given; the batched sumcheck's end
values numbered by `num4`; mk in the place of maskAt; ns so large that the merge's own slots lie
within it. -/
def Plan4L.withMask (QL : Plan4L GE M X) (n0 nT nI ns : ℕ) (mk : M → ℕ → GE) : Plan4L GE M X :=
  { QL with
    n0 := n0
    nT := nT
    nI := nI
    numI := num4 QL.D QL.num
    maskAt := mk
    ns := max ns ((slotsAt QL.D n0 nT nI).f7 + 1 + (2 * QL.kW + 1)) }

/-- **The six choices can be made together**, at every message at once. -/
theorem maskLetters_withMask (QL : Plan4L GE M X) (n0 nT nI ns : ℕ) (mk : M → ℕ → GE) (mm : M) :
    MaskLetters (QL.withMask n0 nT nI ns mk) mm (mk mm) n0 nT nI where
  n0 := rfl
  nT := rfl
  nI := rfl
  numI := rfl
  isM := fun _ _ => rfl
  room := Nat.le_trans (by omega : (slotsAt QL.D n0 nT nI).f7 ≤
    (slotsAt QL.D n0 nT nI).f7 + 1 + (2 * QL.kW + 1)) (Nat.le_max_right _ _)

/-- There the merge's own slots lie within ns too. -/
theorem room7_withMask (QL : Plan4L GE M X) (n0 nT nI ns : ℕ) (mk : M → ℕ → GE) :
    (QL.withMask n0 nT nI ns mk).slots.f7 + 1 + (2 * (QL.withMask n0 nT nI ns mk).plan.kW + 1) ≤
      (QL.withMask n0 nT nI ns mk).ns :=
  Nat.le_max_right _ _

/-- `Meets` reads the sizes and kW alone: it goes over. -/
theorem meets_withMask {QL : Plan4L GE M X} {par : Par} {hS : Layer.Shape}
    {pcl : List (List String)} (A : QL.plan.Meets par hS pcl) (n0 nT nI ns : ℕ)
    (mk : M → ℕ → GE) : (QL.withMask n0 nT nI ns mk).plan.Meets par hS pcl :=
  ⟨A.hy, A.hc, A.hrd, A.Z, A.hl, A.hn, A.wk, A.hg⟩

variable {QL : Plan4L GE M X} {par : Par} {hS : Layer.Shape} {pcl : List (List String)}

/-- **The six ties.** -/
theorem Plan4L.hm_of (A : QL.plan.Meets par hS pcl) {tk : Array Nat} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} (hF : PscRun.Sized F)
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (Ld : Led7 { par.P with tokv := tk } par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2
      G3 G3' G4)
    (mm : M) (mask : ℕ → GE)
    (Lm : MaskLetters QL mm mask F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0)))) :
    (∀ (i : Fin QL.plan.full.D.nNu) (s : Fin 9),
      QL.plan.full.msg mm (QL.plan.full.nr.sq.mkS i s) = mask (H1.sW + 9 * i.val + s.val)) ∧
    QL.plan.full.msg mm QL.plan.full.nr.rows.rJ = mask H1.tV.sCl ∧
    QL.plan.full.msg mm QL.plan.full.rT = mask tT.sCl ∧
    QL.plan.full.msg mm (QL.plan.full.cI (.inl (aH1 QL.plan.full.D))) = mask o.K.sH1 ∧
    (∀ i : Fin QL.plan.full.D.ne,
      QL.plan.full.msg mm (QL.plan.full.cI (.inl (aH2 QL.plan.full.D i))) =
        mask (o.K.sH1 + 1 + i.val)) ∧
    (∀ a : Fin QL.plan.full.nW,
      QL.plan.full.msg mm (QL.plan.full.wp0.wt.nm a) = mask (o.K.sV + a.val)) := by
  have hsl : QL.slots = slotsAt QL.plan.D F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))) := by
    show slotsAt QL.D QL.n0 QL.nT QL.nI = _
    rw [Lm.n0, Lm.nT, Lm.nI]
    rfl
  obtain ⟨a1, _, _, a4, _, _, ⟨tT', e7, a7, _, _⟩, _, a9, _, a11, _⟩ :=
    hear_slotsAt Reading.gl (P := { par.P with tokv := tk }) A.hy A.hrd A.Z A.hl A.hn hF h A.hg
      hsl
  obtain ⟨r1, r2, r3, r4⟩ := slotsAt_within QL.plan.D F.next (nEndT par.P.y)
    (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0)))
  rw [← hsl] at r1 r2 r3 r4
  have room := Lm.room
  have hLam : par.P.y.LamM = QL.plan.D.ne := A.lamM tk
  have hW : QL.plan.nW = par.hp.NCL - (if (par.g == 0) = true then 1 else 0) :=
    OnBytes.Tie.Pv.Lay.At.nW_eq QL.plan.full _ A.dimIs
  have eT : tT'.sCl = tT.sCl := by
    rw [Ld.kTT] at e7
    rw [← Option.some.inj e7]
  refine ⟨fun i s => ?_, ?_, ?_, ?_, fun i => ?_, fun a => ?_⟩
  · have hi : i.val < QL.plan.D.nNu := i.isLt
    have hs := s.isLt
    have hb : QL.plan.sW + 9 * i + s ≤ QL.plan.ns := by
      show QL.slots.sW + 9 * i.val + s.val ≤ QL.ns
      omega
    refine (QL.plan.msg_mkS mm i s hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    show QL.slots.sW + 9 * i.val + s.val = _
    rw [← a1, Ld.kSW]
  · have hb : QL.plan.cP0 ≤ QL.plan.ns := r2.trans room
    refine (QL.plan.msg_rP mm hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    show QL.slots.cP0 = _
    rw [← a4, Ld.kTV]
  · have hb : QL.plan.cT0 ≤ QL.plan.ns := r3.trans room
    refine (QL.plan.msg_rT mm hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    show QL.slots.cT0 = _
    rw [← a7, eT]
  · have e : QL.plan.numI (.inl (aH1 QL.plan.D)) = 1 := by
      show QL.numI _ = 1
      rw [Lm.numI]
      rfl
    have hb : QL.plan.vI + QL.plan.numI (.inl (aH1 QL.plan.D)) ≤ QL.plan.ns := by
      rw [e]
      show QL.slots.vI + 1 ≤ QL.ns
      omega
    refine (QL.plan.msg_cI mm _ hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    rw [e, a9]
    rfl
  · have hi : i.val < QL.plan.D.ne := i.isLt
    have e : QL.plan.numI (.inl (aH2 QL.plan.D i)) = 2 + i.val := by
      show QL.numI _ = _
      rw [Lm.numI]
      rfl
    have hb : QL.plan.vI + QL.plan.numI (.inl (aH2 QL.plan.D i)) ≤ QL.plan.ns := by
      rw [e]
      show QL.slots.vI + (2 + i.val) ≤ QL.ns
      omega
    refine (QL.plan.msg_cI mm _ hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    rw [e, a9]
    show QL.slots.vI + (2 + i.val) = QL.slots.vI + 1 + 1 + i.val
    omega
  · have ha : a.val < QL.plan.nW := a.isLt
    have e : QL.plan.numI (.inr (.inr (QL.plan.num a))) = 2 + (1 + QL.plan.D.ne) + a.val := by
      show QL.numI _ = _
      rw [Lm.numI]
      show 2 + (1 + QL.D.ne) + (QL.num.symm (QL.num a)).val = _
      rw [Equiv.symm_apply_apply]
      rfl
    have hb : QL.plan.vI + QL.plan.numI (.inr (.inr (QL.plan.num a))) ≤ QL.plan.ns := by
      rw [e]
      show QL.slots.vI + (2 + (1 + QL.plan.D.ne) + a.val) ≤ QL.ns
      omega
    refine (QL.plan.msg_cI mm _ hb).trans ((Lm.isM _ hb).trans (congrArg mask ?_))
    rw [e, a11]
    show QL.slots.vI + (2 + (1 + QL.plan.D.ne) + a.val) =
      QL.slots.vI + 1 + (1 + par.P.y.LamM) + 1 + a.val
    omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.slotsAt_within
#print axioms OnBytes.Road.K4.maskLetters_withMask
#print axioms OnBytes.Road.K4.Plan4L.hm_of
