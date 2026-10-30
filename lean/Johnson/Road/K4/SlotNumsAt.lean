-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotNumsAt.lean: the record SlotNums of Johnson/Road/K4/MaskTiesAt.lean, at the plan
whose first slots are the formulas slotsAt (Johnson/Road/K4/ValueSlots.lean), where the hearing of
the layers' own rounds has returned in a group that is not the first.

Johnson/Road/K4/SlotsTie.lean (hear_slotsAt) says that a hearing holds the numbers slotsAt.
Johnson/Road/K4/OwnLedgers.lean (Led7) has the three product layers' calls, from which the right end
value's slot is the left one's plus 1. The slots lie within the mask row if the merge's first own
slot does: the formulas grow.

Main names:
  `room_plain`, `sl_fS` … `sl_f7`, `slotsAt_room`: eight inequalities on slotsAt, from one: over
    plain numbers; the sixteen steps of the formulas, each by definition; the two put together.
  `slotNums_at`: SlotNums at QL.plan; and where the slot of the batched sumcheck's second side lies
    (the premise hsB of stack_of_led, Johnson/Road/K4/SlotsOfLed.lean).
Limits. PREMISES: those of hear_slotsAt; Led7; that the plan's three free numbers n0, nT, nI are the
ledger's next slot in front and the hearing's two numbers of end values; that the plan numbers the
terms' end values as the library does; that the library's number of these end values is at most nT;
that the merge's first own slot is at most ns. Numbers of slots alone. A group that is not the
first.


-/
import Johnson.Road.K4.MaskTiesAt
import Johnson.Road.K4.SlotsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard layout readsOf lamSOf nclOf nEndT)
open OnBytes.Desc.First.P1 (gl levelIn_heard)
open OnBytes.Desc.First.K4 (hear engFl)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)

/-- The inequalities of slotsAt_room, over plain numbers. -/
theorem room_plain {sW fS vS sP cP0 fP vP cT0 fT vT fI vI f5 v5 f6 v6 f7 n a1 a2 a3 a4 a5 a6 nT nI
    ns c : ℕ} (h1 : fS = sW + 9 * n) (h2 : vS = fS + a1) (h3 : sP = vS + 2) (h4 : cP0 = sP + n * 7)
    (h5 : fP = cP0 + 1) (h6 : vP = fP + a2) (h7 : cT0 = vP + 4 * n) (h8 : fT = cT0 + 1)
    (h9 : vT = fT + a3) (h10 : fI = vT + nT) (h11 : vI = fI + a4) (h12 : f5 = vI + nI)
    (h13 : v5 = f5 + a5) (h14 : f6 = v5 + 2) (h15 : v6 = f6 + a6) (h16 : f7 = v6 + 2)
    (h : f7 ≤ ns) (hc : c ≤ nT) :
    sW + 9 * n ≤ ns ∧ vS + 1 ≤ ns ∧ sP + n * 7 ≤ ns ∧ cP0 ≤ ns ∧ vP + 4 * n ≤ ns ∧ vT + c ≤ ns ∧
      v5 + 1 ≤ ns ∧ v6 + 1 ≤ ns := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

section Steps

variable (D : Dim) (n0 nT nI : ℕ)

theorem sl_fS : (slotsAt D n0 nT nI).fS = (slotsAt D n0 nT nI).sW + 9 * D.nNu := rfl
theorem sl_vS : (slotsAt D n0 nT nI).vS = (slotsAt D n0 nT nI).fS +
    (1 + 2 * (D.lL + 1 + (Inst.Model.FFSeg.lDd D + D.lT)) + 2) := rfl
theorem sl_sP : (slotsAt D n0 nT nI).sP = (slotsAt D n0 nT nI).vS + 2 := rfl
theorem sl_cP0 : (slotsAt D n0 nT nI).cP0 = (slotsAt D n0 nT nI).sP + D.nNu * 7 := rfl
theorem sl_fP : (slotsAt D n0 nT nI).fP = (slotsAt D n0 nT nI).cP0 + 1 := rfl
theorem sl_vP : (slotsAt D n0 nT nI).vP = (slotsAt D n0 nT nI).fP + (1 + 2 * D.lT + 2) := rfl
theorem sl_cT0 : (slotsAt D n0 nT nI).cT0 = (slotsAt D n0 nT nI).vP + 4 * D.nNu := rfl
theorem sl_fT : (slotsAt D n0 nT nI).fT = (slotsAt D n0 nT nI).cT0 + 1 := rfl
theorem sl_vT : (slotsAt D n0 nT nI).vT = (slotsAt D n0 nT nI).fT + (1 + 2 * D.lT + 1) := rfl
theorem sl_fI : (slotsAt D n0 nT nI).fI = (slotsAt D n0 nT nI).vT + nT := rfl
theorem sl_vI : (slotsAt D n0 nT nI).vI = (slotsAt D n0 nT nI).fI + (1 + 2 * kS D + 2) := rfl
theorem sl_f5 : (slotsAt D n0 nT nI).f5 = (slotsAt D n0 nT nI).vI + nI := rfl
theorem sl_v5 : (slotsAt D n0 nT nI).v5 = (slotsAt D n0 nT nI).f5 +
    (1 + 2 * (D.lL + Inst.Model.FFSeg.lF D + D.lT) + 2) := rfl
theorem sl_f6 : (slotsAt D n0 nT nI).f6 = (slotsAt D n0 nT nI).v5 + 2 := rfl
theorem sl_v6 : (slotsAt D n0 nT nI).v6 = (slotsAt D n0 nT nI).f6 +
    (1 + 2 * (D.lL - 1 + (Inst.Model.FFSeg.lFe D + D.lT)) + 2) := rfl
theorem sl_f7 : (slotsAt D n0 nT nI).f7 = (slotsAt D n0 nT nI).v6 + 2 := rfl

end Steps

/-- The formulas grow: what lies in front of the merge's first own slot lies within a row that holds
that slot. c: a number of end values of the second token sumcheck, at most nT. -/
theorem slotsAt_room (D : Dim) (n0 nT nI ns c : ℕ) (h : (slotsAt D n0 nT nI).f7 ≤ ns)
    (hc : c ≤ nT) :
    (slotsAt D n0 nT nI).sW + 9 * D.nNu ≤ ns ∧ (slotsAt D n0 nT nI).vS + 1 ≤ ns ∧
      (slotsAt D n0 nT nI).sP + D.nNu * 7 ≤ ns ∧ (slotsAt D n0 nT nI).cP0 ≤ ns ∧
      (slotsAt D n0 nT nI).vP + 4 * D.nNu ≤ ns ∧ (slotsAt D n0 nT nI).vT + c ≤ ns ∧
      (slotsAt D n0 nT nI).v5 + 1 ≤ ns ∧ (slotsAt D n0 nT nI).v6 + 1 ≤ ns :=
  room_plain (sl_fS D n0 nT nI) (sl_vS D n0 nT nI) (sl_sP D n0 nT nI) (sl_cP0 D n0 nT nI)
    (sl_fP D n0 nT nI) (sl_vP D n0 nT nI) (sl_cT0 D n0 nT nI) (sl_fT D n0 nT nI)
    (sl_vT D n0 nT nI) (sl_fI D n0 nT nI) (sl_vI D n0 nT nI) (sl_f5 D n0 nT nI)
    (sl_v5 D n0 nT nI) (sl_f6 D n0 nT nI) (sl_v6 D n0 nT nI) (sl_f7 D n0 nT nI) h hc

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type}

/-- **The plan's numbers are the hearing's.** -/
theorem slotNums_at (QL : Plan4L E' M X) {hS : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} (hy : layout hS pc = .ok P.y)
    (hrd : readsOf P.y = .ok P.rd) (Z : OnBytes.Road.Sized hS QL.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (hF : OnBytes.PscRun.Sized F)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = false)
    (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h0 : QL.n0 = F.next) (hT : QL.nT = nEndT P.y)
    (hI : QL.nI = 2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))
    (hnum : ∀ q, QL.numT q = numA QL.D q)
    (hEnd : QL.D.nNu + QL.D.ne + QL.D.ne * QL.D.nx ≤ QL.nT) (room : QL.slots.f7 ≤ QL.ns) :
    SlotNums QL.plan o ∧ o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM)) := by
  have hs : QL.slots = slotsAt QL.D F.next (nEndT P.y)
      (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))) := by
    unfold Plan4L.slots
    rw [h0, hT, hI]
  obtain ⟨a1, a2, a3, a4, _, a6, ⟨tT', hT', _, _, a7⟩, a8, _, a10, _, a12, ⟨hd2', hh2, a13⟩, _⟩ :=
    hear_slotsAt gl hy hrd Z hl hn hF h hg hs
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
    slotsAt_room QL.D QL.n0 QL.nT QL.nI QL.ns _ room hEnd
  obtain ⟨v1, c1⟩ := Ld.c1
  obtain ⟨v5, c5⟩ := Ld.c5
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s1R, _⟩ := levelIn_heard c1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s5R, _⟩ := levelIn_heard c5
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s6R, _⟩ := levelIn_heard Ld.c6
  refine ⟨?_, by omega⟩
  exact
    { sW := a1.symm
      vS := a2.symm
      sR := by rw [Ld.kWpl]; exact s1R
      sP := a3.symm
      cP0 := a4.symm
      vP := a6.symm
      vT := fun tT2 hT2 => by
        have e : tT2 = tT' := Option.some.inj (hT2.symm.trans hT')
        rw [e]
        exact a7.symm
      numT := hnum
      v5 := a12.symm
      s5R := s5R
      v6 := fun o2 h2 => by
        have e : o2 = hd2' := Option.some.inj (h2.symm.trans hh2)
        rw [e]
        exact a13.symm
      s6R := fun o2 h2 => by
        have e : o2 = hd2 := Option.some.inj (h2.symm.trans Ld.eHd2)
        rw [e]
        exact s6R
      rW := r1
      rS := r2
      rP := r3
      rCl := r4
      r2 := r5
      rT := r6
      r5 := r7
      r6 := r8 }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.room_plain
#print axioms OnBytes.Road.K4.sl_fS
#print axioms OnBytes.Road.K4.sl_vS
#print axioms OnBytes.Road.K4.sl_sP
#print axioms OnBytes.Road.K4.sl_cP0
#print axioms OnBytes.Road.K4.sl_fP
#print axioms OnBytes.Road.K4.sl_vP
#print axioms OnBytes.Road.K4.sl_cT0
#print axioms OnBytes.Road.K4.sl_fT
#print axioms OnBytes.Road.K4.sl_vT
#print axioms OnBytes.Road.K4.sl_fI
#print axioms OnBytes.Road.K4.sl_vI
#print axioms OnBytes.Road.K4.sl_f5
#print axioms OnBytes.Road.K4.sl_v5
#print axioms OnBytes.Road.K4.sl_f6
#print axioms OnBytes.Road.K4.sl_v6
#print axioms OnBytes.Road.K4.sl_f7
#print axioms OnBytes.Road.K4.slotsAt_room
#print axioms OnBytes.Road.K4.slotNums_at
