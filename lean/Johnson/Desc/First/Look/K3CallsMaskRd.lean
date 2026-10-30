-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
att_maskRow_of, lay_maskRow_of: MaskFrameCalls and OneReader are shown of
no state of the verifier and no reader.
Johnson/Desc/First/Look/K3CallsMaskRd.lean: the lookup on a link's CALLS: THE MASK ROW's DICTIONARY
AT A LETTER rd: what the table of joints' data reads at mask entry j THROUGH ANY READER BY SEAT rd
((dataQ own a rd).mask j, Johnson/Desc/Sound/FormsQ.lean) is what the lookup's law reads at the
place "mask j" (attNu | layNu), wherever rd and the witness's typed messages are one at the mask
message (OneReader, Johnson/Desc/First/Att/K05MsgTieOf.lean). The statements of
Johnson/Desc/First/Look/K3CallsMask.lean are the instances at rd := seatTab D.codes arr ms w.
Statements and proofs. A tie of two readings: no error term. NO SOUNDNESS IS CLAIMED.

Why. A law that reads the witness through another reader than seatTab wants the same dictionary; and
at a letter rd nothing is asked of the table's list of members.

OBJECT: Desc.Sound.dataQ; OnPublicFiles.attNu | layNu.
USER: K3HeadObjects.lean (MaskFrameCalls, calls_maskRead_of). att_maskRow_of, lay_maskRow_of: nobody
  yet.
LETTERS: x, A | q, tl, D, rad, seatT, arr, own, a, rd, w, j (and the committed table's at a layers'
  link).
Compiled with the whole library.

Main names:
  `MaskFrameCalls … a`: MaskOkCalls without its field on the list of members: four fields.
  `MaskOkCalls.toFrame`.
  `calls_maskRead_of`: THE CORE, at any tuple of messages m and any reader rd that are one there.
  `att_maskRow_of`, `lay_maskRow_of`: **THE DICTIONARY AT rd.**

Limits. From x.ns on attNu and layNu are 0, whatever the data read.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMask

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
open VerifiableInference.Desc.Sound (Mem MsgT MsgQ dataQ tabQ msgsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs SeatOk ReadMsgOf MsgTieOf msgTieOf_of OneReader
  oracleOfMsg tableOfSeat tableIndex maskOracle_mask)

section
variable {Cells Tok : Type} (x : Desc.First.Look.Place) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (own : List (ℕ × ℕ))

local notation "𝐥" => sigListCalls D rad x.link

/-- **What is asked of the part of the verifier's state.** -/
structure MaskFrameCalls (a : Desc.K9.Part) : Prop where
  frame : FrameIs D x.link a.L.check.frame
  seat : ∀ (j : ℕ) (z : Seat), j < x.ns → seatCalls D x.link (.mask j) = some z →
    ∃ o, oracleOfMsg a.L.check.frame (keptAt D x.link).length z.msg = some o ∧
      ∀ hk : z.msg < 𝐥.length, seatAt own a.d.book o = some (seatT ⟨z.msg, hk⟩)
  one : ∀ o, maskOracle a.L.check.frame = some o → a.d.st.rowBits o .mask = 0
  ns : a.F.ns ≤ x.ns

variable {x D rad seatT own} in
theorem MaskOkCalls.toFrame {ms : List Mem} {a : Desc.K9.Part}
    (M : MaskOkCalls x D rad seatT ms own a) : MaskFrameCalls x D rad seatT own a :=
  ⟨M.frame, M.seat, M.one, M.ns⟩

/-- **THE CORE, AT ANY MESSAGES AND ANY READER THAT ARE ONE AT THE MASK MESSAGE.** -/
theorem calls_maskRead_of (hB : maskCallsB D 𝐥 x.link x.ns = true) (a : Desc.K9.Part)
    (M : MaskFrameCalls x D rad seatT own a) (m : (Johnson.Pack.sigOf D.codes 𝐥).Msg)
    (rd : ℕ × ℕ → MsgQ)
    (h1 : OneReader (ReadMsgOf (maskAddr x.ns) (seatCalls D x.link)) D.codes 𝐥 seatT m rd)
    (j : ℕ) (hj : j < a.F.ns) :
    ∃ z, seatCalls D x.link (.mask j) = some z ∧
      (dataQ own a rd).mask j = (readAt D.codes 𝐥 m z).getD 0 := by
  have hj' : j < x.ns := Nat.lt_of_lt_of_le hj M.ns
  obtain ⟨z, hz, -⟩ := mask_seated hB hj'
  obtain ⟨hzm, hz0, hzj, hw⟩ := maskOracle_mask M.frame hz
  have T : MsgTieOf (maskAddr x.ns) D.codes 𝐥 (seatCalls D x.link) (keptAt D x.link).length
      a.L.check.frame own a.d.st a.d.book rd m :=
    msgTieOf_of (maskAddr x.ns) D.codes 𝐥 (seatCalls D x.link) (keptAt D x.link).length
      a.L.check.frame own a.d.st a.d.book rd m seatT h1
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
    | some o => tabQ own a.d.st a.d.book rd o .mask j
    | none => 0) = _
  rw [hw]
  show _ = tabQ own a.d.st a.d.book rd o .mask (0 + 2 ^ 0 * j)
  rw [pow_zero, Nat.one_mul, Nat.zero_add]

/-- **THE MASK ROW's DICTIONARY AT rd, AT AN ATTENTION LINK.** -/
theorem att_maskRow_of (A : Attention.Shape) (tl : HTailF2)
    (hB : maskCallsB D 𝐥 x.link x.ns = true) (a : Desc.K9.Part)
    (M : MaskFrameCalls x D rad seatT own a) (w : Wit Cells Tok MsgT) (rd : ℕ × ℕ → MsgQ)
    (h1 : OneReader (ReadMsgOf (maskAddr x.ns) (seatCalls D x.link)) D.codes 𝐥 seatT
      (msgsOf D.codes 𝐥 seatT arr w) rd) (j : ℕ) (hj : j < a.F.ns) :
    (dataQ own a rd).mask j = attNu x A tl D rad seatT arr w (.mask j) := by
  obtain ⟨z, hz, e⟩ := calls_maskRead_of x D rad seatT own hB a M _ rd h1 j hj
  rw [e, attNu_maskAt x D rad seatT arr A tl w j (Nat.lt_of_lt_of_le hj M.ns) hz]

/-- **THE MASK ROW's DICTIONARY AT rd, AT A LAYERS' LINK.** -/
theorem lay_maskRow_of (q : LayPub) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)
    (hB : maskCallsB D 𝐥 x.link x.ns = true) (a : Desc.K9.Part)
    (M : MaskFrameCalls x D rad seatT own a) (w : Wit Cells Tok MsgT) (rd : ℕ × ℕ → MsgQ)
    (h1 : OneReader (ReadMsgOf (maskAddr x.ns) (seatCalls D x.link)) D.codes 𝐥 seatT
      (msgsOf D.codes 𝐥 seatT arr w) rd) (j : ℕ) (hj : j < a.F.ns) :
    (dataQ own a rd).mask j = layNu x q tl D rad oW wOf nr nc seatT arr msgW w (.mask j) := by
  obtain ⟨z, hz, e⟩ := calls_maskRead_of x D rad seatT own hB a M _ rd h1 j hj
  rw [e, layNu_maskAt x D rad seatT arr q tl oW wOf nr nc msgW w j (Nat.lt_of_lt_of_le hj M.ns)
    hz]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_maskRead_of
#print axioms VerifiableInference.OnPublicFiles.att_maskRow_of
#print axioms VerifiableInference.OnPublicFiles.lay_maskRow_of
