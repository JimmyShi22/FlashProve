-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
att_maskRow, lay_maskRow: MaskOkCalls is shown of no state of the verifier.
Johnson/Desc/First/Look/K3CallsMask.lean: the lookup on a link's CALLS: THE MASK ROW's DICTIONARY:
what the table of joints' data reads at mask entry j off the witness's tables BY SEAT ((dataQ own a
(seatTab cs arr ms w)).mask j, Johnson/Desc/Sound/FormsQ.lean) IS what the lookup's law reads at the
place "mask j" off the witness's typed messages of the calls' list (attNu … (.mask j),
Johnson/Desc/First/Look/K3AttGoodIn.lean; layNu … (.mask j), K3LayGoodIn.lean). The sister of
Johnson/Desc/First/Look/K3DigitsMask.lean. Statements and proofs. A tie of two readings: no error
term. NO SOUNDNESS IS CLAIMED.

BY A CALL of msgTieOf_at (Johnson/Desc/First/Att/K05MsgTieAt.lean) at l
:= sigListCalls D rad x.link, sf := seatCalls D x.link, kept := (keptAt D x.link).length, and of
maskOracle_mask (K05SeatsOne.lean), which stands at seatCalls.

OBJECT: Desc.Sound.dataQ | seatTab; OnPublicFiles.attNu | layNu.
USER: K3CallsObjects.lean (att_maskRow, lay_maskRow, at the premise hDict of formsT_objects_bare,
  Johnson/Top/H/Keep/FormsTObjects.lean); K3HeadObjects.lean (calls_maskRead).
LETTERS: x, A | q, tl, D, rad, seatT, arr, ms, own, a, w, j (and the committed table's at a layers'
  link).




  Compiled with the whole library.
Main names:
  `MaskOkCalls … a`: WHAT IS ASKED OF THE PART a OF THE VERIFIER's STATE AND OF THE TABLE's LIST OF
    MEMBERS: five fields.
  `calls_maskRead`: THE CORE, whatever the sort of link: the data's mask entry j is what the
    messages hold at the seat of "mask j".
  `attNu_maskAt`, `layNu_maskAt`: so is the lookup's place "mask j", for j below the place's number
    of slots.
  `att_maskRow`, `lay_maskRow`: **THE DICTIONARY**, for j < a.F.ns.

EACH PREMISE, AND WHO COULD PAY IT. hB : maskCallsB D l x.link x.ns = true: a test on public data
(Johnson/Desc/First/Look/K3CallerAttReads.lean): "the mask row reaches the place's number of slots".
MaskOkCalls.frame: four facts on the live request. mem: the table's list of members has a first
member at the mask message's seat, with its shape. seat: the live request has the oracle of that
message, and the book in the verifier's state places it at seatT's seat, which lies in own. one: by
the statement in the verifier's state the mask table of that oracle has one row. ns: the ledger has
at most the place's number of slots.

Limits. From x.ns on attNu and layNu are 0, whatever the data read: so ns is needed.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsMask
import Johnson.Desc.First.Look.K3AttGuards
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Desc.First.Look.K3CallerAttReads
import Johnson.Desc.First.Att.K05SeatsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open Cb.Fo Cb.Fo.NumsEq
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (Mem MsgT dataQ tabQ seatTab msgsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs MemAt SeatOk ReadMsgOf MsgTieOf msgTieOf_at
  oracleOfMsg tableOfSeat tableIndex maskOracle_mask)

section
variable {Cells Tok : Type} (x : Desc.First.Look.Place) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (own : List (ℕ × ℕ))

local notation "𝐥" => sigListCalls D rad x.link

/-- **What is asked of the part of the verifier's state and of the table's list of members.** -/
structure MaskOkCalls (a : Desc.K9.Part) : Prop where
  frame : FrameIs D x.link a.L.check.frame
  mem : ∀ k : Fin 𝐥.length,
    ReadMsgOf (maskAddr x.ns) (seatCalls D x.link) k.val → MemAt ms 𝐥 seatT k
  seat : ∀ (j : ℕ) (z : Seat), j < x.ns → seatCalls D x.link (.mask j) = some z →
    ∃ o, oracleOfMsg a.L.check.frame (keptAt D x.link).length z.msg = some o ∧
      ∀ hk : z.msg < 𝐥.length, seatAt own a.d.book o = some (seatT ⟨z.msg, hk⟩)
  one : ∀ o, maskOracle a.L.check.frame = some o → a.d.st.rowBits o .mask = 0
  ns : a.F.ns ≤ x.ns

/-- **THE CORE: the data's mask entry is what the messages hold at the seat of "mask j".** -/
theorem calls_maskRead (hB : maskCallsB D 𝐥 x.link x.ns = true) (a : Desc.K9.Part)
    (M : MaskOkCalls x D rad seatT ms own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < a.F.ns) :
    ∃ z, seatCalls D x.link (.mask j) = some z ∧
      (dataQ own a (seatTab D.codes arr ms w)).mask j =
        (readAt D.codes 𝐥 (msgsOf D.codes 𝐥 seatT arr w) z).getD 0 := by
  have hj' : j < x.ns := Nat.lt_of_lt_of_le hj M.ns
  obtain ⟨z, hz, -⟩ := mask_seated hB hj'
  obtain ⟨hzm, hz0, hzj, hw⟩ := maskOracle_mask M.frame hz
  have T : MsgTieOf (maskAddr x.ns) D.codes 𝐥 (seatCalls D x.link) (keptAt D x.link).length
      a.L.check.frame own a.d.st a.d.book (seatTab D.codes arr ms w)
      (msgsOf D.codes 𝐥 seatT arr w) :=
    msgTieOf_at (maskAddr x.ns) D.codes 𝐥 (seatCalls D x.link) (keptAt D x.link).length
      a.L.check.frame own a.d.st a.d.book arr seatT ms w M.mem
      (fun ad z' had hs => by
        obtain ⟨j', hj'', rfl⟩ := had
        obtain ⟨z'', hz'', hfit⟩ := mask_seated hB hj''
        obtain rfl : z'' = z' := Option.some.inj (hz''.symm.trans hs)
        obtain ⟨o, ho, hp⟩ := M.seat j' z'' hj'' hz''
        obtain ⟨-, h0, -, -⟩ := maskOracle_mask M.frame hz''
        exact ⟨o, hfit, ho, hp, by rw [h0]; exact Nat.two_pow_pos _⟩)
  obtain ⟨o, ho, hr⟩ := T (.mask j) z ⟨j, hj', rfl⟩ hz
  have hpz : tableOfSeat z = .mask := by
    unfold tableOfSeat
    rw [hzm]
    rfl
  rw [hpz, hz0, hzj] at hr
  rw [ho] at hw
  refine ⟨z, hz, ?_⟩
  rw [hr, M.one o hw]
  show (match maskOracle a.L.check.frame with
    | some o => tabQ own a.d.st a.d.book (seatTab D.codes arr ms w) o .mask j
    | none => 0) = _
  rw [hw]
  show _ = tabQ own a.d.st a.d.book (seatTab D.codes arr ms w) o .mask (0 + 2 ^ 0 * j)
  rw [pow_zero, Nat.one_mul, Nat.zero_add]

/-! ## At an attention link -/

/-- The lookup's place "mask j" is what the messages hold at that address's seat. -/
theorem attNu_maskAt (A : Attention.Shape) (tl : HTailF2) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < x.ns) {z : Seat} (hz : seatCalls D x.link (.mask j) = some z) :
    attNu x A tl D rad seatT arr w (.mask j) =
      (readAt D.codes 𝐥 (msgsOf D.codes 𝐥 seatT arr w) z).getD 0 := by
  rw [attNu_mask x A tl D rad seatT arr w j hj]
  unfold valAt
  rw [hz]
  rfl

/-- **THE MASK ROW's DICTIONARY, AT AN ATTENTION LINK.** -/
theorem att_maskRow (A : Attention.Shape) (tl : HTailF2)
    (hB : maskCallsB D 𝐥 x.link x.ns = true) (a : Desc.K9.Part)
    (M : MaskOkCalls x D rad seatT ms own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < a.F.ns) :
    (dataQ own a (seatTab D.codes arr ms w)).mask j =
      attNu x A tl D rad seatT arr w (.mask j) := by
  obtain ⟨z, hz, e⟩ := calls_maskRead x D rad seatT arr ms own hB a M w j hj
  rw [e, attNu_maskAt x D rad seatT arr A tl w j (Nat.lt_of_lt_of_le hj M.ns) hz]

/-! ## At a layers' link -/

/-- The lookup's place "mask j" is what the messages hold at that address's seat. -/
theorem layNu_maskAt (q : LayPub) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)
    (w : Wit Cells Tok MsgT) (j : ℕ) (hj : j < x.ns) {z : Seat}
    (hz : seatCalls D x.link (.mask j) = some z) :
    layNu x q tl D rad oW wOf nr nc seatT arr msgW w (.mask j) =
      (readAt D.codes 𝐥 (msgsOf D.codes 𝐥 seatT arr w) z).getD 0 := by
  have e : lyMask x.ns tl nr nc j = some (Sum.inl (Sum.inl ⟨j, hj⟩)) := by
    unfold lyMask
    rw [finOf_some hj]
    rfl
  show layMu x tl D rad oW wOf nr nc seatT arr msgW w (lyMask x.ns tl nr nc j) = _
  rw [e]
  show (valAt D.codes 𝐥 (seatCalls D x.link) (msgsOf D.codes 𝐥 seatT arr w) (.mask j)).getD 0 = _
  unfold valAt
  rw [hz]
  rfl

/-- **THE MASK ROW's DICTIONARY, AT A LAYERS' LINK.** -/
theorem lay_maskRow (q : LayPub) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)
    (hB : maskCallsB D 𝐥 x.link x.ns = true) (a : Desc.K9.Part)
    (M : MaskOkCalls x D rad seatT ms own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < a.F.ns) :
    (dataQ own a (seatTab D.codes arr ms w)).mask j =
      layNu x q tl D rad oW wOf nr nc seatT arr msgW w (.mask j) := by
  obtain ⟨z, hz, e⟩ := calls_maskRead x D rad seatT arr ms own hB a M w j hj
  rw [e, layNu_maskAt x D rad seatT arr q tl oW wOf nr nc msgW w j (Nat.lt_of_lt_of_le hj M.ns) hz]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_maskRead
#print axioms VerifiableInference.OnPublicFiles.att_maskRow
#print axioms VerifiableInference.OnPublicFiles.lay_maskRow
