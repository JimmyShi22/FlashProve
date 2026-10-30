-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/CellsAtHead.lean: THE KIND K9 (a link's batching): THE TWO TESTS ON PUBLIC DATA THAT
THE SENTENCE cells OF hLeft STILL NAMES (hT1 : seatsPubB · hT2 : shapesPubB: the binders of
P5J.AtMgA.left_cells, Johnson/P5J/K09LeftCells.lean), AT EACH OF THE 25 LINKS, FROM THE HEAD ALONE,
AT THE CLOSED LETTERS At.…, WHICH ARE THE COMPOSED MEANING's PARAMETERS' OWN FIELDS
(Johnson/P5J/LettersAll.lean). At every o; at every radii.
THE ARGUMENT, as in Johnson/P2LawR/MasksAtHead.lean, whose congruences and ties are called: the
tests read the request's shape · of the table's numbers msgsAt and sent alone · the plan's seats ·
the listed seats and shapes · closed lists. Under the head each is a written term; at the written
terms Lean's kernel has decided (Johnson/P2LawR/CellsWritten.lean).
  seatsPub_congr · shapesPub_congr   the tests read msgsAt alone of the numbers.
  own1_congr · ownAt_any   the planned numbers of a link's own messages, at every moment.
  last_congr · sig_len · sig_fst · ofFn_len the list of the link's own messages hangs on the shape
      alone, in its length and its shapes.
  cellSeats_congr · cellShapes_congr   so the two tests' texts.
  **AtMg.hT1_cells · AtMg.hT2_cells**   the two.
Limits. xx.link = m IS A PREMISE (el): left_cells has it in its own proof. hB | hZ (laidArrB)
AND h3 ARE NOT HERE. NO MEMBER: that a head can be had is not said. The full size alone. At the
door's list of thirteen rows alone. (Where this and
lean/THEOREM.md differ, the page holds.) Nothing on soundness.

-/
import Johnson.P2LawR.CellsWritten
import Johnson.P2LawR.MasksAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K9C
open OnBytes
open VerifiableInference.OnPublicFiles (bookedB)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.LinkJoin (seatsPubB shapesPubB)
open VerifiableInference.Desc.First (Numbers ModelPart)
open VerifiableInference.Desc.First.Look (Sent messagesAt sigList lastMoment)
open VerifiableInference.Desc.First.FillSent (sentDataAt sentData1At base1At base2At secondNos
  thirdNos ownAt)
open VerifiableInference.Desc.K12.Door (Laid)
open P2Law.K3M (own_congr base1_congr base2_congr group_congr)

theorem seatsPub_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (nos : Array ℕ)
    (p : Option Place) (Ld : Laid) (own seats : List (ℕ × ℕ)) :
    seatsPubB nos N p Ld own seats = seatsPubB nos N' p Ld own seats := by
  unfold seatsPubB bookedB
  rw [hm]

theorem shapesPub_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (nos : Array ℕ)
    (p : Option Place) (M shapes : List OracleShape) :
    shapesPubB nos N p M shapes = shapesPubB nos N' p M shapes := by
  unfold shapesPubB bookedB
  rw [hm]

theorem own1_congr {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (S : Params.ReqShape)
    (links : List ModelPart) (ps : List Place) (b b' : Array Model.Stages.LinkH) (m : ℕ) :
    (sentData1At S N links ps b).own m = (sentData1At S N' links ps b').own m := by
  show (sentDataAt S N links ps b).own m ++ secondNos S (base1At N links ps) m =
    (sentDataAt S N' links ps b').own m ++ secondNos S (base1At N' links ps) m
  rw [own_congr hm S links ps b b' m, base1_congr hm]

/-- The planned numbers of a link's own messages, at every moment. -/
theorem ownAt_any {N N' : Numbers} (hm : N.msgsAt = N'.msgsAt) (S : Params.ReqShape)
    (links : List ModelPart) (ps : List Place) (b b' : Array Model.Stages.LinkH) (m j : ℕ) :
    ownAt S N links ps b m j = ownAt S N' links ps b' m j := by
  unfold VerifiableInference.Desc.First.FillSent.ownAt
  rw [own_congr hm S links ps b b' m, own1_congr hm S links ps b b' m, base2_congr hm]

theorem last_congr {D D' : Sent} (hS : D.shape = D'.shape) (i : ℕ) :
    lastMoment D i = lastMoment D' i := by
  unfold VerifiableInference.Desc.First.Look.lastMoment messagesAt
  rw [hS]

theorem sig_len {D D' : Sent} (hS : D.shape = D'.shape) (rad rad' : OracleShape → ℕ)
    (i mom : ℕ) : (sigList D rad i mom).length = (sigList D' rad' i mom).length := by
  unfold VerifiableInference.Desc.First.Look.sigList messagesAt
  rw [hS, List.length_map, List.length_map]

theorem sig_fst {D D' : Sent} (hS : D.shape = D'.shape) (rad rad' : OracleShape → ℕ)
    (i mom : ℕ) : (sigList D rad i mom).map (·.1) = (sigList D' rad' i mom).map (·.1) := by
  unfold VerifiableInference.Desc.First.Look.sigList messagesAt
  rw [hS, List.map_map, List.map_map]
  rfl

theorem ofFn_len {α : Type} (f : ℕ → α) {n n' : ℕ} (h : n = n') :
    (List.ofFn fun j : Fin n => f j.1) = List.ofFn fun j : Fin n' => f j.1 := by
  subst h
  rfl

/-- **seatsPubB's text hangs on the shape, msgsAt, sent and the plan's seats alone.** -/
theorem cellSeats_congr (D D' : Sent) (hS : D.shape = D'.shape) {N N' : Numbers}
    (hm : N.msgsAt = N'.msgsAt) (hs : N.sent = N'.sent) (rad rad' : OracleShape → ℕ)
    (ps : List P5T.PSeat) (links : List ModelPart) (pl : List Place)
    (b b' : Array Model.Stages.LinkH) (p : Option Place) (Ld : Laid) (m j : ℕ) :
    seatsPubB (ownAt D.shape N links pl b m j) N p Ld (N.group m)
        (List.ofFn fun i : Fin (sigList D rad m (lastMoment D m)).length => P6T.seatT ps m i.1) =
      seatsPubB (ownAt D'.shape N' links pl b' m j) N' p Ld (N'.group m)
        (List.ofFn fun i : Fin (sigList D' rad' m (lastMoment D' m)).length =>
          P6T.seatT ps m i.1) := by
  have hl : (sigList D rad m (lastMoment D m)).length =
      (sigList D' rad' m (lastMoment D' m)).length := by
    rw [last_congr hS m]
    exact sig_len hS rad rad' m _
  rw [seatsPub_congr hm, group_congr hs, hS, ownAt_any hm D'.shape links pl b b' m j,
    ofFn_len (fun i => P6T.seatT ps m i) hl]

/-- **shapesPubB's text likewise.** -/
theorem cellShapes_congr (D D' : Sent) (hS : D.shape = D'.shape) {N N' : Numbers}
    (hm : N.msgsAt = N'.msgsAt) (rad rad' : OracleShape → ℕ) (links : List ModelPart)
    (pl : List Place) (b b' : Array Model.Stages.LinkH) (p : Option Place)
    (M : List OracleShape) (m j : ℕ) :
    shapesPubB (ownAt D.shape N links pl b m j) N p M
        ((sigList D rad m (lastMoment D m)).map (·.1)) =
      shapesPubB (ownAt D'.shape N' links pl b' m j) N' p M
        ((sigList D' rad' m (lastMoment D' m)).map (·.1)) := by
  rw [shapesPub_congr hm, hS, ownAt_any hm D'.shape links pl b b' m j, last_congr hS m,
    sig_fst hS rad rad' m _]

end P2Law.K9C

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (seatsPubB shapesPubB batchAt)
open VerifiableInference.Desc.First (momentAt shiftAt)
open VerifiableInference.Desc.First.Look (digList sigList lastMoment)
open VerifiableInference.Desc.First.FillSent (ownAt)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open P2Law.K3M (sentW numsW)
open P2Law.K9C

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **hT1 AT EACH OF THE 25 LINKS, FROM THE HEAD ALONE.** -/
theorem AtMg.hT1_cells (h : AtMg o Z D r Zp Np cF) {Ld : Laid} (hL : At.laid? Zp = some Ld)
    {m : ℕ} (hm : m < 25) {xx : VerifiableInference.Desc.First.Look.Place} (el : xx.link = m)
    {p : VerifiableInference.Desc.Place} (hp : At.ps[batchAt fullLinks At.ps m]? = some p)
    (rad : OracleShape → ℕ) :
    seatsPubB ((At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece)) (At.N Zp cF)
      (some p) Ld ((At.N Zp cF).group m)
      (List.ofFn fun j : Fin (digList xx (At.sentAt Zp) rad).length =>
        At.seat3At Zp xx.link true j.1) = true := by
  obtain rfl : LFull = Ld := Option.some.inj (h.laid_at_head.symm.trans hL)
  subst el
  have hq : At.pseats Zp = P5T.psFull := h.seats
  have t : cellSeatsW 0 xx.link = true :=
    List.all_eq_true.1 cellSeats_written xx.link (List.mem_range.2 hm)
  unfold cellSeatsW at t
  rw [hp] at t
  show seatsPubB (ownAt (At.sentAt Zp).shape (At.N Zp cF) At.links At.ps Zp.made.p.built.links
      xx.link (momentAt (shiftAt At.links xx.link) p.piece)) (At.N Zp cF) (some p) LFull
    ((At.N Zp cF).group xx.link)
    (List.ofFn fun j : Fin (sigList (At.sentAt Zp) rad xx.link
        (lastMoment (At.sentAt Zp) xx.link)).length =>
      P6T.seatT (At.pseats Zp) xx.link j.1) = true
  rw [hq, cellSeats_congr (At.sentAt Zp) sentW h.masks_shape_written h.msgs_fn h.sent_fn rad
    (fun _ => 0) P5T.psFull At.links At.ps Zp.made.p.built.links #[] (some p) LFull xx.link _]
  exact t

/-- **hT2 AT EACH OF THE 25 LINKS, FROM THE HEAD ALONE.** -/
theorem AtMg.hT2_cells (h : AtMg o Z D r Zp Np cF) (Ld : Laid) {m : ℕ} (hm : m < 25)
    {xx : VerifiableInference.Desc.First.Look.Place} (el : xx.link = m)
    {p : VerifiableInference.Desc.Place} (hp : At.ps[batchAt fullLinks At.ps m]? = some p)
    (rad : OracleShape → ℕ) :
    shapesPubB ((At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece)) (At.N Zp cF)
      (some p) (msgsOfChain Zp.made.proof.1) ((digList xx (At.sentAt Zp) rad).map (·.1)) =
        true := by
  subst el
  rw [h.msgs_at_head]
  have t : cellShapesW MFull xx.link = true :=
    List.all_eq_true.1 cellShapes_written xx.link (List.mem_range.2 hm)
  unfold cellShapesW at t
  rw [hp] at t
  show shapesPubB (ownAt (At.sentAt Zp).shape (At.N Zp cF) At.links At.ps Zp.made.p.built.links
      xx.link (momentAt (shiftAt At.links xx.link) p.piece)) (At.N Zp cF) (some p) MFull
    ((sigList (At.sentAt Zp) rad xx.link (lastMoment (At.sentAt Zp) xx.link)).map (·.1)) = true
  rw [cellShapes_congr (At.sentAt Zp) sentW h.masks_shape_written h.msgs_fn rad (fun _ => 0)
    At.links At.ps Zp.made.p.built.links #[] (some p) MFull xx.link _]
  exact t

end P5J

#print axioms P2Law.K9C.seatsPub_congr
#print axioms P2Law.K9C.shapesPub_congr
#print axioms P2Law.K9C.own1_congr
#print axioms P2Law.K9C.ownAt_any
#print axioms P2Law.K9C.last_congr
#print axioms P2Law.K9C.sig_len
#print axioms P2Law.K9C.sig_fst
#print axioms P2Law.K9C.ofFn_len
#print axioms P2Law.K9C.cellSeats_congr
#print axioms P2Law.K9C.cellShapes_congr
#print axioms P5J.AtMg.hT1_cells
#print axioms P5J.AtMg.hT2_cells
