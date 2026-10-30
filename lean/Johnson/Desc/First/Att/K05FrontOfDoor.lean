-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05FrontOfDoor.lean: kind K5: ALL THAT THE UPPER JOINT ASKS IN FRONT OF THE
KIND's BLOCK (FrontAll, Johnson/Desc/First/Att/K05BehindWorth.lean) FROM "THE DOOR's BOOLS SAY YES
AT THE VERIFIER's STATE, AND FIVE EQUATIONS".

IS IT EMPTY HERE? NO MEMBER IS SHOWN: of the Bools none has run at a state of a run in this library.

WHERE IT PAYS: at the state IN FRONT of the kind's block (piece 3), where the six Bools' items are
open. Behind the block three of them are dropped by the kind's own row: there FrontAll is had by
frontAll_rides (Johnson/Desc/First/Att/K05FrontRides.lean).

Main names:
  `secL_of_reads`: the door's Bool on the array of the reads (readsThereB) gives SecL at the open
    link: the field array of U3There is its text.
  `frontAll_of_door`: **FrontAll**, from DoorYes (Johnson/Desc/First/Att/K05DoorYes.lean),
    W.A[x.link / 2]? = some A and OfPlan A.
CALLED: width_of_sheet, u3There_of_sheet
(Johnson/Desc/First/Att/Door/Law/ReadsThereTie.lean) · plannedK_of_plan
(Johnson/Desc/First/Att/K05PlannedK.lean) · sized_of_B, fork_front
(Johnson/Desc/First/Att/K05BehindLay.lean). Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindWorth
import Johnson.Desc.First.Att.K05DoorYes
import Johnson.Desc.First.Att.K05SeatReadsTie
import Johnson.Desc.First.Att.Door.Law.ReadsThereTie
import Johnson.Desc.First.Att.K05PlannedK

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Sent keptAt bornAt)
open H2K5.Door (readsThereB lookAttB width_of_sheet u3There_of_sheet)
open K5Law (OfPlan)

/-- The door's Bool on the array of the reads gives SecL at the open link. -/
theorem secL_of_reads {W : Verify.Public} {own : List (ℕ × ℕ)} {s : First.S} {a : First.AttOwn}
    {A : Attention.Plan} (e : s.here = .att a) (hp : W.A[a.L.link / 2]? = some A)
    (h : readsThereB W own s = true) : SecL a.L A.iU3 := by
  obtain ⟨b, Ar, hb, hA, hm, _, _⟩ := (u3There_of_sheet W own s a e A hp h).array
  exact ⟨b, Ar, hb, hA, hm⟩

/-- **All that is asked in front, from the door's yes.** -/
theorem frontAll_of_door {W : Verify.Public} {x : VerifiableInference.Desc.First.Look.Place}
    {A : Attention.Plan} {D : Sent} {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ} {gL : Forest.Heard} {s : First.S}
    (hA : W.A[x.link / 2]? = some A) (hP : OfPlan A)
    (Y : DoorYes W x D (bornAt D x.link) (keptAt D x.link).length own ps qs hi gL s) : FrontAll x A D own ps qs hi gL s := by
  obtain ⟨L, hL, hlink, hshape, hlay, harr, hcodes⟩ := Y.link
  cases hs : s.here with
  | att a =>
    have eL : a.L = L := by
      have := hL
      unfold First.S.link? at this
      rw [hs] at this
      exact Option.some.inj this
    have hp : W.A[a.L.link / 2]? = some A := by rw [eL, hlink]; exact hA
    have hsec : SecL L A.iU3 := eL ▸ secL_of_reads hs hp Y.reads
    have hthere : (L.arrayOf[A.iU3]?).isSome = true := by
      obtain ⟨b, _, hb, _⟩ := hsec
      rw [hb]
      rfl
    refine ⟨⟨L, ⟨Y.live, Y.seats, Y.shapes, hlink, hshape, hlay, harr, hcodes, hL, hthere⟩⟩,
      fun F hF => ?_, seatReads_of_look Y.look Y.heard, plain_of_look Y.look Y.heard,
      fun L' hL' => (Option.some.inj (hL.symm.trans hL')) ▸ hsec⟩
    have eF : a.F = F := by
      unfold seatSO at hF
      simp only [hs] at hF
      exact Option.some.inj hF
    have ef := fork_front hs
    have hz := Y.sized
    rw [ef] at hz
    obtain ⟨T, hT, hR1, hK⟩ := width_of_sheet W own s a hs A hp Y.reads
    rw [← eF]
    exact ⟨sized_of_B hz, Y.ns _ ef, T, hT, hK.trans (plannedK_of_plan hP).symm, Nat.le_of_eq hK.symm,
      hR1⟩
  | _ =>
    have := Y.look
    unfold lookAttB H2K5.Door.lookAttUpTo at this
    simp only [hs] at this
    cases this

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.secL_of_reads
#print axioms VerifiableInference.Desc.First.Att.P.frontAll_of_door
