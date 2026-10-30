-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/MasksAtHead.lean: THE KIND "LOOKUP" (K3): TWO OF THE MASKS' THREE TESTS UNDER THE
HEAD: hTests (maskTestsB: ×25 at the calls, ×25 at the digits) AND h6 (oneShapeB: ×1), AT THE CLOSED
LETTERS At.…, WHICH ARE THE COMPOSED MEANING's PARAMETERS' OWN FIELDS (Johnson/P5J/LettersAll.lean).
FROM THE HEAD ALONE. At every o.
THE ARGUMENT. The tests read: the request's shape · of the table's numbers msgsAt and sent alone ·
the plan's seats · the listed seats and shapes · closed lists. No test reads a radius, a table of
names, the layout or the built segments (calls_congr · digits_congr · oneShape_at say so: the other
letters are free in them). Under the head each of these is a written term: first_written_in_scope
(MadeInScope.lean) · told_at_head · laid_at_head · msgs_at_head (PlanSitsCore.lean); AtMg.seats ·
N_six (CoreAtMg.lean). At the written terms Lean's kernel has decided (MasksWritten.lean).
  tests_congr · own_congr · ownAt_congr · group_congr   what the pieces read of the numbers.
  calls_congr · digits_congr the two tests' texts hang on the shape, msgsAt, sent and the seats
      alone.
  oneShape_at oneShapeB at the members by the make, at any radii, from shapesP at the plan's seats:
      over P5T.memsSame_atR (Johnson/P5T/MembersByMake.lean).
  AtMg.masks_shape_written · msgs_fn · sent_fn   the ties.
  **AtMg.hTests_calls · AtMg.hTests_digits · AtMg.h6_at_head** the three, in the texts of
      ObjEndR | DigTestsR's fields (Johnson/P5J/K03End.lean | K03Due4.lean) at x.link := l.
Limits. THE THIRD TEST, hB, IS NOT HERE: it reads the place's number of slots, which no pin holds
below the head's segment. x.link = l is VerifiableInference.OnPublicFiles.lookAt_link's to give.
AtMg.masks_shape_written says again what P5J.AtMg.shape_written says
(Johnson/HB/LLHARD/MaskSeatWritten.lean: not among the files over which this was first compiled)
and a part of what P5J.sent_at_head says (Johnson/P5J/K03TieAt.lean): that file stands over
Johnson/Desc/First/Look/K3IdxAt.lean. NO MEMBER: that a head can be had is not said. The full size
alone. At the door's list of thirteen rows alone.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.

-/
import Johnson.P2LawR.MasksWritten
import Johnson.P5J.PlanSitsCore
import Johnson.P5J.Rad3Seat3At
import Johnson.P5J.FoldAt
import Johnson.P5T.CoreAtMg
import Johnson.P5T.MembersByMake
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K3M
open OnBytes
open VerifiableInference.OnPublicFiles (maskTestsB bookedB maskOwnIx oneShapeB k3K)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Numbers ModelPart toldCut flatPlacesOf)
open VerifiableInference.Desc.First.Look (Sent keptAt)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.First.FillSent (sentDataAt sentData1At sentDataOf baseAt base1At
  base2At secondNos thirdNos laterOf ownAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.Sound (Mem seatOf msOf)

/-- The test reads msgsAt alone of the numbers. -/
theorem tests_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (kM? : Option ℕ) (kept : ℕ)
    (nos : Array ℕ) (p : Option Place) (Ld : Laid) (M : List OracleShape) (own : List (ℕ × ℕ))
    (seatN : ℕ → ℕ × ℕ) :
    maskTestsB kM? kept nos N p Ld M own seatN = maskTestsB kM? kept nos N' p Ld M own seatN := by
  unfold maskTestsB bookedB
  rw [hm]

theorem base_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (links : List ModelPart)
    (ps : List Place) : baseAt N links ps = baseAt N' links ps := by
  funext m
  unfold baseAt
  rw [hm]

theorem base1_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (links : List ModelPart)
    (ps : List Place) : base1At N links ps = base1At N' links ps := by
  funext m
  unfold base1At
  rw [hm]

theorem base2_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (links : List ModelPart)
    (ps : List Place) : base2At N links ps = base2At N' links ps := by
  funext m
  unfold base2At
  rw [hm]

/-- The planned numbers of a segment's own messages read the shape and msgsAt alone. -/
theorem own_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (S : Params.ReqShape)
    (links : List ModelPart) (ps : List Place) (b b' : Array Model.Stages.LinkH) (m : ℕ) :
    (sentDataAt S N links ps b).own m = (sentDataAt S N' links ps b').own m := by
  unfold sentDataAt
  rw [base_congr hm]
  rfl

theorem ownAt_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (S : Params.ReqShape)
    (links : List ModelPart) (ps : List Place) (b b' : Array Model.Stages.LinkH) (m : ℕ) :
    ownAt S N links ps b m 3 = ownAt S N' links ps b' m 3 := by
  show (sentData1At S N links ps b).own m ++ thirdNos S (base2At N links ps) m =
    (sentData1At S N' links ps b').own m ++ thirdNos S (base2At N' links ps) m
  show ((sentDataAt S N links ps b).own m ++ secondNos S (base1At N links ps) m) ++
      thirdNos S (base2At N links ps) m =
    ((sentDataAt S N' links ps b').own m ++ secondNos S (base1At N' links ps) m) ++
      thirdNos S (base2At N' links ps) m
  rw [own_congr hm S links ps b b' m, base1_congr hm, base2_congr hm]

theorem group_congr {N N' : Numbers} (hs : N.sent = N'.sent) (l : ℕ) : N.group l = N'.group l := by
  unfold Numbers.group
  rw [hs]

/-- **The test at the calls hangs on the shape, msgsAt, sent and the plan's seats alone.** -/
theorem calls_congr (D D' : Sent) (hS : D.shape = D'.shape) {N N' : Numbers}
    (hm : N.msgsAt = N'.msgsAt) (hs : N.sent = N'.sent) (ps : List P5T.PSeat) (links : List ModelPart)
    (pl : List Place) (b b' : Array Model.Stages.LinkH) (p : Option Place) (Ld : Laid)
    (M : List OracleShape) (l : ℕ) :
    maskTestsB (maskMsg D l) (keptAt D l).length ((sentDataAt D.shape N links pl b).own l) N p Ld M
        (N.sent l 0) (fun j => P6T.seatCallsT ps D l j) =
      maskTestsB (maskMsg D' l) (keptAt D' l).length ((sentDataAt D'.shape N' links pl b').own l) N'
        p Ld M (N'.sent l 0) (fun j => P6T.seatCallsT ps D' l j) := by
  obtain ⟨c, s, lay, A⟩ := D
  obtain ⟨c', s', lay', A'⟩ := D'
  obtain rfl : s = s' := hS
  rw [tests_congr hm, hs]
  show maskTestsB _ _ ((sentDataAt s N links pl b).own l) _ _ _ _ _ _ =
    maskTestsB _ _ ((sentDataAt s N' links pl b').own l) _ _ _ _ _ _
  rw [own_congr hm s links pl b b' l]
  rfl

/-- **The test at the digits likewise.** -/
theorem digits_congr (D D' : Sent) (hS : D.shape = D'.shape) {N N' : Numbers}
    (hm : N.msgsAt = N'.msgsAt) (hs : N.sent = N'.sent) (ps : List P5T.PSeat) (links : List ModelPart)
    (pl : List Place) (b b' : Array Model.Stages.LinkH) (p : Option Place) (Ld : Laid)
    (M : List OracleShape) (l : ℕ) :
    maskTestsB (maskOwnIx D l) 0 (ownAt D.shape N links pl b l 3) N p Ld M (N.group l)
        (fun j => P6T.seatT ps l j) =
      maskTestsB (maskOwnIx D' l) 0 (ownAt D'.shape N' links pl b' l 3) N' p Ld M (N'.group l)
        (fun j => P6T.seatT ps l j) := by
  obtain ⟨c, s, lay, A⟩ := D
  obtain ⟨c', s', lay', A'⟩ := D'
  obtain rfl : s = s' := hS
  rw [tests_congr hm, group_congr hs]
  show maskTestsB _ _ (ownAt s N links pl b l 3) _ _ _ _ _ _ =
    maskTestsB _ _ (ownAt s N' links pl b' l 3) _ _ _ _ _ _
  rw [ownAt_congr hm s links pl b b' l]
  rfl

/-- **"One seat, one shape" at the members by the make, at any radii.** -/
theorem oneShape_at (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ)
    (h : shapesP (·.seat) (P5T.planSeats Z Z.D.1) = true) :
    oneShapeB (P5T.msAtR Z rad) = true := by
  unfold shapesP at h
  unfold oneShapeB
  rw [List.all_eq_true]
  intro y hy
  rw [List.all_eq_true]
  intro y' hy'
  by_cases hq : seatOf y = seatOf y'
  · obtain ⟨p, hp, ep⟩ := List.mem_map.1 ((P5T.memsSame_atR Z rad _).1
      (List.mem_map_of_mem (f := fun x : Mem => ((x.1.l.get x.2).1, seatOf x)) hy))
    obtain ⟨p', hp', ep'⟩ := List.mem_map.1 ((P5T.memsSame_atR Z rad _).1
      (List.mem_map_of_mem (f := fun x : Mem => ((x.1.l.get x.2).1, seatOf x)) hy'))
    have a1 : p.shape = (y.1.l.get y.2).1 := congrArg Prod.fst ep
    have a2 : p.seat = seatOf y := congrArg Prod.snd ep
    have b1 : p'.shape = (y'.1.l.get y'.2).1 := congrArg Prod.fst ep'
    have b2 : p'.seat = seatOf y' := congrArg Prod.snd ep'
    have t : (!decide (p.seat = p'.seat) || p.shape == p'.shape) = true :=
      List.all_eq_true.1 (List.all_eq_true.1 h p hp) p' hp'
    rw [decide_eq_true (a2.trans (hq.trans b2.symm)), Bool.not_true, Bool.false_or] at t
    rw [decide_eq_true hq, Bool.not_true, Bool.false_or, ← a1, ← b1]
    exact t
  · rw [decide_eq_false hq]
    rfl

end P2Law.K3M

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.OnPublicFiles (maskTestsB maskOwnIx oneShapeB k3K)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.First.Look (keptAt)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.First.FillSent (sentDataAt ownAt)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.Desc.Sound (linksFull)
open P2Law.K3M

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Under the head the request's shape is the written one. -/
theorem AtMg.masks_shape_written (h : AtMg o Z D r Zp Np cF) : At.shape Zp = sentW.shape :=
  (VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
    h.made_accepts).2.2.1.trans VerifiableInference.PlanWritten.request_shape_written

/-- Under the head the numbers of messages at the borders are the written ones. -/
theorem AtMg.msgs_fn (h : AtMg o Z D r Zp Np cF) : (At.N Zp cF).msgsAt = numsW.msgsAt := by
  unfold At.N
  rw [h.told_at_head]
  rfl

/-- Under the head the sampled tenants by segment and moment are the written ones. -/
theorem AtMg.sent_fn (h : AtMg o Z D r Zp Np cF) : (At.N Zp cF).sent = numsW.sent := h.N_six.1

/-- **hTests AT THE CALLS, AT EACH OF THE 25 SEGMENTS, FROM THE HEAD ALONE.** -/
theorem AtMg.hTests_calls (h : AtMg o Z D r Zp Np cF) {L : Laid} (hL : At.laid? Zp = some L)
    {l : ℕ} (hl : l < 25) :
    maskTestsB (maskMsg (At.sentAt Zp) l) (keptAt (At.sentAt Zp) l).length
      ((sentDataAt (At.shape Zp) (At.N Zp cF) At.links (flatPlacesOf At.links true)
        Zp.made.p.built.links).own l) (At.N Zp cF) (flatPlacesOf linksFull true)[k3K l false + 1]?
      L (msgsOfChain Zp.made.proof.1) ((At.N Zp cF).sent l 0) (At.seat3At Zp l false) = true := by
  obtain rfl : LFull = L := Option.some.inj (h.laid_at_head.symm.trans hL)
  rw [h.msgs_at_head]
  have hp : At.pseats Zp = P5T.psFull := h.seats
  show maskTestsB (maskMsg (At.sentAt Zp) l) (keptAt (At.sentAt Zp) l).length
    ((sentDataAt (At.sentAt Zp).shape (At.N Zp cF) At.links At.ps Zp.made.p.built.links).own l)
    (At.N Zp cF) (flatPlacesOf linksFull true)[k3K l false + 1]? LFull MFull
    ((At.N Zp cF).sent l 0) (fun j => P6T.seatCallsT (At.pseats Zp) (At.sentAt Zp) l j) = true
  rw [hp, calls_congr (At.sentAt Zp) sentW h.masks_shape_written h.msgs_fn h.sent_fn P5T.psFull
    At.links At.ps Zp.made.p.built.links #[] _ LFull MFull l]
  exact List.all_eq_true.1 calls_written l (List.mem_range.2 hl)

/-- **hTests AT THE DIGITS, AT EACH OF THE 25 SEGMENTS, FROM THE HEAD ALONE.** -/
theorem AtMg.hTests_digits (h : AtMg o Z D r Zp Np cF) {L : Laid} (hL : At.laid? Zp = some L)
    {l : ℕ} (hl : l < 25) :
    maskTestsB (maskOwnIx (At.sentAt Zp) l) 0 ((At.foldD Zp cF L).ownAt l 3) (At.N Zp cF)
      (flatPlacesOf linksFull true)[k3K l true + 1]? L (msgsOfChain Zp.made.proof.1)
      ((At.N Zp cF).group l) (At.seat3At Zp l true) = true := by
  obtain rfl : LFull = L := Option.some.inj (h.laid_at_head.symm.trans hL)
  rw [h.msgs_at_head]
  have hp : At.pseats Zp = P5T.psFull := h.seats
  show maskTestsB (maskOwnIx (At.sentAt Zp) l) 0
    (ownAt (At.sentAt Zp).shape (At.N Zp cF) At.links At.ps Zp.made.p.built.links l 3)
    (At.N Zp cF) (flatPlacesOf linksFull true)[k3K l true + 1]? LFull MFull
    ((At.N Zp cF).group l) (fun j => P6T.seatT (At.pseats Zp) l j) = true
  rw [hp, digits_congr (At.sentAt Zp) sentW h.masks_shape_written h.msgs_fn h.sent_fn P5T.psFull
    At.links At.ps Zp.made.p.built.links #[] _ LFull MFull l]
  exact List.all_eq_true.1 digits_written l (List.mem_range.2 hl)

/-- **h6, FROM THE HEAD ALONE.** -/
theorem AtMg.h6_at_head (h : AtMg o Z D r Zp Np cF) : oneShapeB (At.ms Zp Z.lay) = true := by
  refine oneShape_at Zp (At.rad Zp Z.lay) ?_
  rw [h.seats]
  exact P2Law.K3M.shapes_written

end P5J

#print axioms P2Law.K3M.tests_congr
#print axioms P2Law.K3M.base_congr
#print axioms P2Law.K3M.base1_congr
#print axioms P2Law.K3M.base2_congr
#print axioms P2Law.K3M.own_congr
#print axioms P2Law.K3M.ownAt_congr
#print axioms P2Law.K3M.group_congr
#print axioms P2Law.K3M.calls_congr
#print axioms P2Law.K3M.digits_congr
#print axioms P2Law.K3M.oneShape_at
#print axioms P5J.AtMg.masks_shape_written
#print axioms P5J.AtMg.msgs_fn
#print axioms P5J.AtMg.sent_fn
#print axioms P5J.AtMg.hTests_calls
#print axioms P5J.AtMg.hTests_digits
#print axioms P5J.AtMg.h6_at_head
