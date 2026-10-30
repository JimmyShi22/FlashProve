-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsMask.lean: MaskOk is shown of no state of
the verifier. The lookup on the approximate range proof's digits: THE MASK ROW's DICTIONARY: what
the table of joints' data reads at mask entry j off the witness's tables BY SEAT (dataQ own a
(seatTab cs arr ms w)).mask j, Johnson/Desc/Sound/FormsQ.lean, BordersFill.lean) IS what the
lookup's law reads at the place «mask j» off the witness's typed messages of the link's own list
(digNu … (.mask j), Johnson/Desc/First/Look/K3DigitsGoodIn.lean). One theorem with two small
lemmas. A tie of two readings: no error term. GENERAL IN THE READER rd OF THE
WITNESS's TABLES BY SEAT, under "the two readers are one" (OneReader) at the member that holds the
mask row. BY A CALL of msgTieOf_of
(Johnson/Desc/First/Att/K05MsgTieOf.lean: general in the list, the seats' function, the number of
kept messages and the reader), at l := digList x D rad, sf := Look.seatOf D x.link, kept := 0.

  maskAddr n: the addresses «mask j», j < n.
  maskOracle_own: which message holds the mask row: the two writings are one, at Look.seatOf and no
  kept message (the like of maskOracle_mask, K05SeatsOne.lean, which stands at seatCalls).
  digNu_mask: digNu … (.mask j) is what the messages hold at the seat of «mask j», for j <
  x.arrays.ns.
  MaskOkR … a: what is asked of the state's part a: four fields. MaskOk … a: these and mem (on the
  table's list of members): five fields.
  digits_maskRow_of: **THE DICTIONARY**, for j < a.F.ns, at any reader rd with OneReader.
  digits_maskRow: its instance at rd := seatTab D.codes arr ms w (oneReader_at under MaskOk.mem).
OBJECT: Desc.Sound.dataQ | seatTab · OnPublicFiles.digNu. USER:
Johnson/Top/H/Keep/DigitsRestPays.lean calls digits_maskRow_of; FormsObjectsDigits.lean, in the same
folder, calls digits_maskRow.
LETTERS: x, tl, D, rad, seatT, arr, ms, own, a, w, j.
Compiled with the whole library.
EACH PREMISE, AND WHO COULD PAY IT. hB : maskB D (digList x D rad) x.link x.arrays.ns = true: A
PUBLIC Bool (Look/K3CallerLaid.lean:257; the digits' own test digB asks it only up to x.F.next + the
lookup's masks): «the mask row reaches the number of slots»: there is the like
at the calls' list as a law of the planner's return (masks_of_built) · MaskOk.frame: four facts on
the live request (FrameIs: its shape is D's; its link is x.link; born; next): the promise in front ·
mem: the table's list of members has a first member at the mask message's seat, with its shape
(MemAt): a Bool, given ms with code · seat: the live request has the oracle of that message, and THE
STATE's BOOK PLACES IT AT seatT's SEAT, WHICH LIES IN own: the promise in front (seatsAtB,
Johnson/Desc/First/Att/K05DoorB.lean, is such a Bool) ·
one: by the state's statement the mask table of that oracle has one row (0 row bits): the promise
in front, with «one mask row» of the plan · ns: the state's ledger has at most the planned number
of slots: the promise in front.
Limits. From x.arrays.ns on digNu is 0, whatever the data read: so ns is needed. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05MsgTieAt
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.Look.K3CallerLaid

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
open VerifiableInference.Desc.Sound (Mem MsgT MsgQ dataQ tabQ seatTab msgsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs MemAt SeatOk ReadMsgOf MsgTieOf msgTieOf_of
  OneReader oneReader_at oracleOfMsg tableOfSeat tableIndex)

/-- The addresses «mask j», j < n. -/
def maskAddr (n : ℕ) (a : Addr) : Prop := ∃ j, j < n ∧ a = .mask j

/-- **Which message holds the mask row: the two writings are one**, at the link's own list. -/
theorem maskOracle_own {D : Sent} {i : ℕ} {f : ReqFrame} (H : FrameIs D i f) {j : ℕ} {z : Seat}
    (hz : seatOf D i (.mask j) = some z) :
    z.mask = true ∧ z.row = 0 ∧ z.place = j ∧ maskOracle f = oracleOfMsg f 0 z.msg := by
  unfold seatOf at hz
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hz
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold maskOracle oracleOfMsg ReqFrame.whereIs
  unfold messagesAt at hm
  rw [H.shape, H.link, hm, H.next]
  simp

section
variable {Cells Tok : Type} (x : Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

/-- The lookup's place «mask j» is what the messages hold at that address's seat. -/
theorem digNu_mask (w : Wit Cells Tok MsgT) (j : ℕ) (hj : j < x.arrays.ns) {z : Seat}
    (hz : seatOf D x.link (.mask j) = some z) :
    digNu x tl D rad seatT arr w (.mask j) =
      (readAt D.codes (digList x D rad) (msgsOf D.codes (digList x D rad) seatT arr w) z).getD
        0 := by
  have hf : findJ x.arrays (.mask j) = some (Sum.inr ⟨j, hj⟩) := by
    show (finOf x.arrays.ns j).map Sum.inr = _
    rw [finOf_some hj]
    rfl
  show msgAt D.codes (digList x D rad) (seatOf D x.link) x.arrays
    (msgsOf D.codes (digList x D rad) seatT arr w) (findJ x.arrays (.mask j)) = _
  rw [msgAt_of D.codes (digList x D rad) (seatOf D x.link) x.arrays hf]
  unfold valAt
  rw [hz]
  rfl

variable (ms : List Mem) (own : List (ℕ × ℕ))

/-- **What is asked of the state's part.** -/
structure MaskOkR (a : Desc.K9.Part) : Prop where
  frame : FrameIs D x.link a.L.check.frame
  seat : ∀ (j : ℕ) (z : Seat), j < x.arrays.ns → seatOf D x.link (.mask j) = some z →
    ∃ o, oracleOfMsg a.L.check.frame 0 z.msg = some o ∧
      ∀ hk : z.msg < (digList x D rad).length,
        seatAt own a.d.book o = some (seatT ⟨z.msg, hk⟩)
  one : ∀ o, maskOracle a.L.check.frame = some o → a.d.st.rowBits o .mask = 0
  ns : a.F.ns ≤ x.arrays.ns

/-- **What is asked of the state's part and of the table's list of members.** -/
structure MaskOk (a : Desc.K9.Part) : Prop where
  frame : FrameIs D x.link a.L.check.frame
  mem : ∀ k : Fin (digList x D rad).length,
    ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link) k.val → MemAt ms (digList x D rad) seatT k
  seat : ∀ (j : ℕ) (z : Seat), j < x.arrays.ns → seatOf D x.link (.mask j) = some z →
    ∃ o, oracleOfMsg a.L.check.frame 0 z.msg = some o ∧
      ∀ hk : z.msg < (digList x D rad).length,
        seatAt own a.d.book o = some (seatT ⟨z.msg, hk⟩)
  one : ∀ o, maskOracle a.L.check.frame = some o → a.d.st.rowBits o .mask = 0
  ns : a.F.ns ≤ x.arrays.ns

variable {x D rad seatT ms own} in
theorem MaskOk.r {a : Desc.K9.Part} (M : MaskOk x D rad seatT ms own a) :
    MaskOkR x D rad seatT own a := ⟨M.frame, M.seat, M.one, M.ns⟩

/-- **THE MASK ROW's DICTIONARY, at any reader of the witness's tables by seat.** -/
theorem digits_maskRow_of (hB : maskB D (digList x D rad) x.link x.arrays.ns = true)
    (rd : ℕ × ℕ → MsgQ) (w : Wit Cells Tok MsgT)
    (h1 : OneReader (ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link)) D.codes
      (digList x D rad) seatT (msgsOf D.codes (digList x D rad) seatT arr w) rd)
    (a : Desc.K9.Part) (M : MaskOkR x D rad seatT own a) (j : ℕ) (hj : j < a.F.ns) :
    (dataQ own a rd).mask j = digNu x tl D rad seatT arr w (.mask j) := by
  have hj' : j < x.arrays.ns := Nat.lt_of_lt_of_le hj M.ns
  obtain ⟨z, hz, -⟩ := mask_resolves hB hj'
  obtain ⟨hzm, hz0, hzj, hw⟩ := maskOracle_own M.frame hz
  have T : MsgTieOf (maskAddr x.arrays.ns) D.codes (digList x D rad) (seatOf D x.link) 0
      a.L.check.frame own a.d.st a.d.book rd
      (msgsOf D.codes (digList x D rad) seatT arr w) :=
    msgTieOf_of (maskAddr x.arrays.ns) D.codes (digList x D rad) (seatOf D x.link) 0
      a.L.check.frame own a.d.st a.d.book rd (msgsOf D.codes (digList x D rad) seatT arr w) seatT
      h1
      (fun ad z' had hs => by
        obtain ⟨j', hj'', rfl⟩ := had
        obtain ⟨z'', hz'', hfit⟩ := mask_resolves hB hj''
        obtain rfl : z'' = z' := Option.some.inj (hz''.symm.trans hs)
        obtain ⟨o, ho, hp⟩ := M.seat j' z'' hj'' hz''
        obtain ⟨-, h0, -, -⟩ := maskOracle_own M.frame hz''
        exact ⟨o, hfit, ho, hp, by rw [h0]; exact Nat.two_pow_pos _⟩)
  obtain ⟨o, ho, hr⟩ := T (.mask j) z ⟨j, hj', rfl⟩ hz
  have hpz : tableOfSeat z = .mask := by
    unfold tableOfSeat
    rw [hzm]
    rfl
  rw [hpz, hz0, hzj] at hr
  rw [ho] at hw
  rw [digNu_mask x tl D rad seatT arr w j hj' hz, hr, M.one o hw]
  show (match maskOracle a.L.check.frame with
    | some o => tabQ own a.d.st a.d.book rd o .mask j
    | none => 0) = _
  rw [hw]
  show _ = tabQ own a.d.st a.d.book rd o .mask (0 + 2 ^ 0 * j)
  rw [pow_zero, Nat.one_mul, Nat.zero_add]

/-- **THE MASK ROW's DICTIONARY**, at the table's own reader. -/
theorem digits_maskRow (hB : maskB D (digList x D rad) x.link x.arrays.ns = true)
    (a : Desc.K9.Part) (M : MaskOk x D rad seatT ms own a) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < a.F.ns) :
    (dataQ own a (seatTab D.codes arr ms w)).mask j = digNu x tl D rad seatT arr w (.mask j) :=
  digits_maskRow_of x tl D rad seatT arr own hB (seatTab D.codes arr ms w) w
    (oneReader_at _ D.codes arr (digList x D rad) seatT ms w M.mem) a M.r j hj

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.maskOracle_own
#print axioms VerifiableInference.OnPublicFiles.digNu_mask
#print axioms VerifiableInference.OnPublicFiles.digits_maskRow_of
#print axioms VerifiableInference.OnPublicFiles.digits_maskRow
