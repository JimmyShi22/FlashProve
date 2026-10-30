-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/MasksK.lean: at the plan whose first slots are the formulas slotsAt
(Johnson/Road/K4/ValueSlots.lean), where the hearing of the layers' own rounds has returned in a
group that is not the first: the messages at the names of the mask entries are the mask row at the
hearing's own slots: the record MaskTies (Johnson/Road/K4/SlotsOfLed.lean), and the two mask entries
of the batched sumcheck's two form parts.

Main names:
  `room_vI`: an inequality on the formulas, over plain numbers.
  `masks_K`: MaskTies at every tuple of messages m and all late entries u (maskTies_at over
    slotNums_at); and the messages at the names of the two form parts' mask entries are the mask row
    at o.K.sA0 and o.K.sB0 (Plan4.msg_cI, Johnson/Road/K4/ValueMasks.lean; hear_slotsAt,
    Johnson/Road/K4/SlotsTie.lean).
Limits. PREMISES: those of slotNums_at (Johnson/Road/K4/SlotNumsAt.lean); that the plan numbers the
two form parts' end values 0 and 2 + ne; LamM = ne. Numbers of slots and names alone. A group that
is not the first. Nothing on soundness.


-/
import Johnson.Road.K4.SlotNumsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard layout readsOf lamSOf nclOf nEndT)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Desc.First.K4 (hear engFl)
open Inst.Model (Scl)

/-- What lies among the batched sumcheck's end values lies within a row that holds the merge's first
own slot: over plain numbers. -/
theorem room_vI {vI f5 v5 f6 v6 f7 nI a5 a6 ns c : ℕ} (h12 : f5 = vI + nI) (h13 : v5 = f5 + a5)
    (h14 : f6 = v5 + 2) (h15 : v6 = f6 + a6) (h16 : f7 = v6 + 2) (h : f7 ≤ ns) (hc : c ≤ nI) :
    vI + c ≤ ns := by
  omega

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type}

/-- **The messages at the mask entries' names are the mask row at the hearing's slots.** -/
theorem masks_K (QL : Plan4L E' M X) {hS : OnBytes.Model.Layer.Shape}
    {pc : List (List String)} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard}
    {o : Own} {F G : Fork} {t0 u0 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} (hy : layout hS pc = .ok P.y)
    (hrd : readsOf P.y = .ok P.rd) (Z : OnBytes.Road.Sized hS QL.D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (hF : OnBytes.PscRun.Sized F)
    (h : hear engFl P hp g fo F t0 = some (o, G, u0)) (hg : (g == 0) = false)
    (Ld : Led7 P hp g fo o F G t0 u0 H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h0 : QL.n0 = F.next) (hT : QL.nT = nEndT P.y)
    (hI : QL.nI = 2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))
    (hnum : ∀ q, QL.numT q = numA QL.D q)
    (hEnd : QL.D.nNu + QL.D.ne + QL.D.ne * QL.D.nx ≤ QL.nT) (room : QL.slots.f7 ≤ QL.ns)
    (hIA : QL.numI (Sum.inl (Sum.inl ())) = 0) (hIB : QL.numI (Sum.inr (Sum.inl ())) = 2 + QL.D.ne)
    (hLM : P.y.LamM = QL.D.ne) (m : M) {J₂ : Type} (u : J₂ → E') (UN : NormsReads J₂)
    (UT : TermsReads J₂) (UG : GatedReads J₂) :
    MaskTies (QL.plan.maskAt m) o QL.plan.full.D (namesAt QL.plan.full.nr UN)
        (namesT QL.plan.full.tp UT) (gNamesAt QL.plan.full.fp UG)
        (Sum.elim (QL.plan.full.msg m) u) ∧
      QL.plan.full.msg m (QL.plan.full.ip.cI (Sum.inl (Sum.inl ()))) =
        QL.plan.maskAt m o.K.sA0 ∧
      QL.plan.full.msg m (QL.plan.full.ip.cI (Sum.inr (Sum.inl ()))) =
        QL.plan.maskAt m o.K.sB0 := by
  have hs : QL.slots = slotsAt QL.D F.next (nEndT P.y)
      (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))) := by
    unfold Plan4L.slots
    rw [h0, hT, hI]
  obtain ⟨_, _, _, _, _, _, _, a8, _, _⟩ := hear_slotsAt gl hy hrd Z hl hn hF h hg hs
  obtain ⟨Sn, hsB⟩ := slotNums_at QL hy hrd Z hl hn hF h hg Ld h0 hT hI hnum hEnd room
  have rm : ∀ c, c ≤ QL.nI → QL.slots.vI + c ≤ QL.ns := fun c hc =>
    room_vI (sl_f5 QL.D QL.n0 QL.nT QL.nI) (sl_v5 QL.D QL.n0 QL.nT QL.nI)
      (sl_f6 QL.D QL.n0 QL.nT QL.nI) (sl_v6 QL.D QL.n0 QL.nT QL.nI)
      (sl_f7 QL.D QL.n0 QL.nT QL.nI) room hc
  have eA : QL.slots.vI + QL.numI (Sum.inl (Sum.inl ())) = o.K.sA0 := by
    rw [hIA, a8]
    rfl
  have eB : QL.slots.vI + QL.numI (Sum.inr (Sum.inl ())) = o.K.sB0 := by
    rw [hIB, hsB, a8, hLM]
    omega
  refine ⟨maskTies_at QL.plan m u Sn UN UT UG, ?_, ?_⟩
  · exact (QL.plan.msg_cI m (Sum.inl (Sum.inl ())) (by
      show QL.slots.vI + QL.numI (Sum.inl (Sum.inl ())) ≤ QL.ns
      rw [hIA]
      exact rm 0 (Nat.zero_le _))).trans (congrArg (QL.plan.maskAt m) eA)
  · exact (QL.plan.msg_cI m (Sum.inr (Sum.inl ())) (by
      show QL.slots.vI + QL.numI (Sum.inr (Sum.inl ())) ≤ QL.ns
      rw [hIB]
      exact rm _ (by rw [hI, hLM]; omega))).trans (congrArg (QL.plan.maskAt m) eB)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.room_vI
#print axioms OnBytes.Road.K4.masks_K
