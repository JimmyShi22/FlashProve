-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/MasksKFirst.lean: at the first group's value whose first slots are the formulas
slotsAt (`Plan4LF.planF`, Johnson/Road/K4/ValueSlotsFirst.lean), where the hearing of the layers'
own rounds has returned in the first group: the messages at the names of the mask entries are the
mask row at the hearing's own slots: the record MaskTies (Johnson/Road/K4/SlotsOfLed.lean), and the
two mask entries of the batched sumcheck's two form parts. The twin of
Johnson/Road/K4/SlotNumsAt.lean's `slotNums_at` and of Johnson/Road/K4/MasksK.lean's `masks_K`. Two
theorems: their proofs at these letters, over `hear_slotsAtF` (HwTiesFirst.lean) and `LedG`
(OwnLedgersG.lean).

  `slotNums_atF`: SlotNums (MaskTiesAt.lean) at QF.planF.toPlan4; and where the slot of the batched
    sumcheck's second side lies.
  `masks_KF`: MaskTies at every tuple of messages m and all late entries u (`maskTies_at`, which
    stands at every `Plan4`); and the messages at the names of the two form parts' mask entries are
    the mask row at o.K.sA0 and o.K.sB0.

What is other than in a later group: nothing in the statements but the letters. SlotNums reads no
slot behind the routed gated layer's end values, so the embedding's slot and the merge's first own
slot, which alone lie otherwise in the first group, are not spoken of.

Limits. K04_law IS NOT PROVED BY THIS. PREMISES: the layout is `layout`'s, the reads' numbers
`readsOf`'s, the sizes agree with the shape, lamS and NCL are the plan's · the ledger in front has
arrays of the right sizes · the hearing's return, in the first group, and `LedG` at it · the value's
three free numbers n0, nT, nI are the ledger's next slot in front and the hearing's two numbers of
end values · the value numbers the terms' end values as the library does, and the library's number
of these is at most nT · the formula f7 is at most ns · for `masks_KF`: the value numbers the two
form parts' end values 0 and 2 + ne; LamM = ne. Numbers of slots and names alone. Nothing on
soundness.
-/
import Johnson.Road.K4.MasksK
import Johnson.Road.K4.HwTiesFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard layout readsOf lamSOf nclOf nEndT)
open OnBytes.Desc.First.P1 (gl levelIn_heard)
open OnBytes.Desc.First.K4 (hear engFl)
open Inst.Model (Scl)

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type}

/-- **The first group's value's numbers are the hearing's**, under the premises that the head
lists. -/
theorem slotNums_atF (QF : Plan4LF E' M X) {hS : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} (hy : layout hS pc = .ok P.y)
    (hrd : readsOf P.y = .ok P.rd) (Z : OnBytes.Road.Sized hS QF.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (hF : OnBytes.PscRun.Sized F)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = true)
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h0 : QF.n0 = F.next) (hT : QF.nT = nEndT P.y)
    (hI : QF.nI = 2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))
    (hnum : ∀ q, QF.numT q = numA QF.D q)
    (hEnd : QF.D.nNu + QF.D.ne + QF.D.ne * QF.D.nx ≤ QF.nT)
    (room : QF.toPlan4L.slots.f7 ≤ QF.ns) :
    SlotNums QF.planF.toPlan4 o ∧ o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM)) := by
  have hs : QF.toPlan4L.slots = slotsAt QF.D F.next (nEndT P.y)
      (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))) := by
    unfold Plan4L.slots
    rw [h0, hT, hI]
  obtain ⟨a1, a2, a3, a4, _, a6, ⟨tT', hT', _, _, a7⟩, a8, _, a10, _, a12, ⟨hd2', hh2, a13⟩, _,
    _⟩ := hear_slotsAtF gl hy hrd Z hl hn hF h hg hs
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
    slotsAt_room QF.D QF.n0 QF.nT QF.nI QF.ns _ room hEnd
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

/-- **The messages at the mask entries' names are the mask row at the hearing's slots, in the first
group**, under the premises that the head lists. -/
theorem masks_KF (QF : Plan4LF E' M X) {hS : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard}
    {o : Own} {F G : Fork} {t0 u0 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} (hy : layout hS pc = .ok P.y)
    (hrd : readsOf P.y = .ok P.rd) (Z : OnBytes.Road.Sized hS QF.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (hF : OnBytes.PscRun.Sized F)
    (h : hear engFl P hp g fo F t0 = some (o, G, u0)) (hg : (g == 0) = true)
    (Ld : LedG P hp g fo o F G t0 u0 H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h0 : QF.n0 = F.next) (hT : QF.nT = nEndT P.y)
    (hI : QF.nI = 2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))
    (hnum : ∀ q, QF.numT q = numA QF.D q)
    (hEnd : QF.D.nNu + QF.D.ne + QF.D.ne * QF.D.nx ≤ QF.nT)
    (room : QF.toPlan4L.slots.f7 ≤ QF.ns)
    (hIA : QF.numI (Sum.inl (Sum.inl ())) = 0) (hIB : QF.numI (Sum.inr (Sum.inl ())) = 2 + QF.D.ne)
    (hLM : P.y.LamM = QF.D.ne) (m : M) {J₂ : Type} (u : J₂ → E') (UN : NormsReads J₂)
    (UT : TermsReads J₂) (UG : GatedReads J₂) :
    MaskTies (QF.planF.maskAt m) o QF.planF.fullF.D (namesAt QF.planF.fullF.ofp.nr UN)
        (namesT QF.planF.fullF.tp UT) (gNamesAt QF.planF.fullF.fp UG)
        (Sum.elim (QF.planF.fullF.msg m) u) ∧
      QF.planF.fullF.msg m (QF.planF.fullF.ip.cI (Sum.inl (Sum.inl ()))) =
        QF.planF.maskAt m o.K.sA0 ∧
      QF.planF.fullF.msg m (QF.planF.fullF.ip.cI (Sum.inr (Sum.inl ()))) =
        QF.planF.maskAt m o.K.sB0 := by
  have hs : QF.toPlan4L.slots = slotsAt QF.D F.next (nEndT P.y)
      (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))) := by
    unfold Plan4L.slots
    rw [h0, hT, hI]
  obtain ⟨_, _, _, _, _, _, _, a8, _, _⟩ := hear_slotsAtF gl hy hrd Z hl hn hF h hg hs
  obtain ⟨Sn, hsB⟩ := slotNums_atF QF hy hrd Z hl hn hF h hg Ld h0 hT hI hnum hEnd room
  have rm : ∀ c, c ≤ QF.nI → QF.toPlan4L.slots.vI + c ≤ QF.ns := fun c hc =>
    room_vI (sl_f5 QF.D QF.n0 QF.nT QF.nI) (sl_v5 QF.D QF.n0 QF.nT QF.nI)
      (sl_f6 QF.D QF.n0 QF.nT QF.nI) (sl_v6 QF.D QF.n0 QF.nT QF.nI)
      (sl_f7 QF.D QF.n0 QF.nT QF.nI) room hc
  have eA : QF.toPlan4L.slots.vI + QF.numI (Sum.inl (Sum.inl ())) = o.K.sA0 := by
    rw [hIA, a8]
    rfl
  have eB : QF.toPlan4L.slots.vI + QF.numI (Sum.inr (Sum.inl ())) = o.K.sB0 := by
    rw [hIB, hsB, a8, hLM]
    omega
  refine ⟨maskTies_at QF.planF.toPlan4 m u Sn UN UT UG, ?_, ?_⟩
  · exact (QF.planF.toPlan4.msg_cI m (Sum.inl (Sum.inl ())) (by
      show QF.toPlan4L.slots.vI + QF.numI (Sum.inl (Sum.inl ())) ≤ QF.ns
      rw [hIA]
      exact rm 0 (Nat.zero_le _))).trans (congrArg (QF.planF.maskAt m) eA)
  · exact (QF.planF.toPlan4.msg_cI m (Sum.inr (Sum.inl ())) (by
      show QF.toPlan4L.slots.vI + QF.numI (Sum.inr (Sum.inl ())) ≤ QF.ns
      rw [hIB]
      exact rm _ (by rw [hI, hLM]; omega))).trans (congrArg (QF.planF.maskAt m) eB)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.slotNums_atF
#print axioms OnBytes.Road.K4.masks_KF
