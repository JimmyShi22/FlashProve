-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/DigitsCell.lean: The kind "lookup" (K3), at the lookup on the approximate range
proof's digits: THE DICTIONARY ON CELLS: at every cell that the first four claims of the run
"K8.equations" read (the counts' array BZ: 32 rows; the pieces of the digits' array ZZ), what the
witness's messages hold at the cell's seat, as the closed caller reads them (digVal), IS THE CELL
OF THE TABLE OF JOINTS' DATA (dataQ off the witness's tables, Johnson/Desc/Sound/FormsQ.lean).
Definitions, statements and proofs: the sister, at cells, of
Johnson/Desc/First/Look/K3DigitsMask.lean; after the first arm of
addrTie_of (Johnson/Desc/First/Att/K05AddrTieOf.lean), at another
list of members. GENERAL IN THE READER rd OF THE WITNESS's TABLES BY SEAT AND IN THE
TUPLE OF MESSAGES m, under "the two readers are one" (OneReader) at the members that hold the read
cells.

OBJECT: digVal at msgsOf of the witness; dataQ at seatTab of the witness; K8.Four.cellOf.
USER: Johnson/Top/H/Keep/DigitsRestPays.lean (cellAddr, CellOkR, CellOk);
  Johnson/Desc/First/Link/Law/CellOkAt.lean (cellAddr, whereIs_own, CellOkR);
  Johnson/Desc/First/Link/Law/CellTests.lean (cellAddr, CellOkR); and others.
  Meant: the premises hcb and hcz of Johnson/Top/H/Keep/EquationsPlanesKeys.lean and
  of Johnson/Desc/First/Look/K3DigitsAtWorld.lean [not in this library].
LETTERS: x, tl, D, rad, seatT, arr, ms, own; a: the part of the verifier's state; w.

Main names:
  cellAddr tl: the addresses that hcb and hcz range over.
  whereIs_own: which message holds a cell of the link's own: the two writings are one.
  CellOkR: what is asked of the state's part. CellOk: that, and mem (on the table's list of
    members).
  digits_cellRow_of: THE END, at any reader rd with OneReader. digits_hcb_of, digits_hcz_of: in the
    two premises' own forms.
  digits_cellRow, digits_hcb, digits_hcz: the instances at rd := seatTab D.codes arr ms w and m :=
    msgsOf of the witness (oneReader_at under CellOk.mem).

Limits. dataQ READS AN ARRAY WHOSE MESSAGE IS NOT YET SENT AS 0. CellOk.seat asks that the message
which holds the cell has its number in the state's live request: THAT CAN HOLD ONLY WHERE THAT
MESSAGE IS SENT: so CellOk is meant at the batching's row, where all the segment's sendings are
sent; at an earlier border it fails, aloud. CellOk is shown of no state. hs (the address has a
seat): under DigOK: dig_cell_bz, dig_cell_zz (Johnson/Desc/First/Look/K3DigRows.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieAt
import Johnson.Desc.First.Att.K05CellAt
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.K8.Four.AtWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params OnBytes.DgP
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9L (dataOf)
open VerifiableInference.Desc.Sound (Mem MsgT MsgQ dataQ tabQ seatTab msgsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (cellOf unknownOf)
open VerifiableInference.Desc.First.Att.P (FrameIs MemAt SeatOk ReadMsgOf MsgTieOf msgTieOf_of
  OneReader oneReader_at oracleOfMsg tableOfSeat tableIndex dataOf_cell)

/-- The addresses that the first four claims read. -/
def cellAddr (tl : HTailF2) (ad : Addr) : Prop :=
  (∃ r i, r < 32 ∧ i < tl.bzColumns ∧ ad = .cell tl.ix.BZ r i) ∨
    ∃ q p r i, q < 2 ∧ p ∈ piecesL tl q ∧ r < p.Rp ∧ i < p.Cp ∧
      ad = .cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)

/-- **Which message holds a cell of the link's own: the two writings are one.** -/
theorem whereIs_own {D : Sent} {i : ℕ} {f : ReqFrame} (H : FrameIs D i f) {t r c : ℕ} {z : Seat}
    (hz : seatOf D i (.cell t r c) = some z) :
    ∃ bn a, (D.arrayOf.getD i #[])[t]? = some bn ∧ reqArray D.layout bn.1 bn.2 = some a ∧
      laidPlace a.blocks r c = some (z.row, z.place) ∧ z.mask = false ∧
      f.whereIs bn.1 a.message = oracleOfMsg f 0 z.msg := by
  unfold seatOf at hz
  obtain ⟨bn, hbn, hz⟩ := Option.bind_eq_some_iff.1 hz
  by_cases hb : (bn.1 == i) = true
  · rw [if_pos hb] at hz
    obtain ⟨a, ha, hz⟩ := Option.bind_eq_some_iff.1 hz
    obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.1 hz
    have hbi : bn.1 = i := by simpa using hb
    refine ⟨bn, a, hbn, by rw [hbi]; exact ha, hrp, rfl, ?_⟩
    unfold ReqFrame.whereIs oracleOfMsg
    rw [H.next, H.link]
    simp [hb]
  · rw [if_neg hb] at hz
    exact nomatch hz

section
variable {Cells Tok : Type} (x : Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (own : List (ℕ × ℕ))

/-- **What is asked of the state's part.** -/
structure CellOkR (a : Desc.K9.Part) : Prop where
  frame : FrameIs D x.link a.L.check.frame
  lay : a.L.check.rows.layout = D.layout
  arr : a.L.arrayOf = D.arrayOf.getD x.link #[]
  seat : ∀ (ad : Addr) (z : Seat), cellAddr tl ad → seatOf D x.link ad = some z →
    ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o
  laid : ∀ (t r c : ℕ) (bn : ℕ × String) (a' : ReqArray) (o : ℕ), cellAddr tl (.cell t r c) →
    (D.arrayOf.getD x.link #[])[t]? = some bn → reqArray D.layout bn.1 bn.2 = some a' →
    a.L.check.frame.whereIs bn.1 a'.message = some o →
    laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true

/-- **What is asked of the state's part and of the table's list of members.** -/
structure CellOk (a : Desc.K9.Part) : Prop where
  frame : FrameIs D x.link a.L.check.frame
  lay : a.L.check.rows.layout = D.layout
  arr : a.L.arrayOf = D.arrayOf.getD x.link #[]
  mem : ∀ k : Fin (digList x D rad).length,
    ReadMsgOf (cellAddr tl) (seatOf D x.link) k.val → MemAt ms (digList x D rad) seatT k
  seat : ∀ (ad : Addr) (z : Seat), cellAddr tl ad → seatOf D x.link ad = some z →
    ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o
  laid : ∀ (t r c : ℕ) (bn : ℕ × String) (a' : ReqArray) (o : ℕ), cellAddr tl (.cell t r c) →
    (D.arrayOf.getD x.link #[])[t]? = some bn → reqArray D.layout bn.1 bn.2 = some a' →
    a.L.check.frame.whereIs bn.1 a'.message = some o →
    laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true

variable {x tl D rad seatT ms own} in
theorem CellOk.r {a : Desc.K9.Part} (C : CellOk x tl D rad seatT ms own a) :
    CellOkR x tl D rad seatT own a := ⟨C.frame, C.lay, C.arr, C.seat, C.laid⟩

/-- **THE DICTIONARY ON CELLS, at any reader of the witness's tables by seat.** -/
theorem digits_cellRow_of (rd : ℕ × ℕ → MsgQ) (m : (digSg x D rad).Msg)
    (h1 : OneReader (ReadMsgOf (cellAddr tl) (seatOf D x.link)) D.codes (digList x D rad) seatT m
      rd)
    (a : Desc.K9.Part) (C : CellOkR x tl D rad seatT own a) (t r c : ℕ)
    (had : cellAddr tl (.cell t r c))
    (hs : (seatOf D x.link (.cell t r c)).isSome = true) :
    digVal x D rad m (.cell t r c) = some (cellOf a.L (dataQ own a rd) t r c) := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨bn, a', hbn, ha, hp, hzm, hw⟩ := whereIs_own C.frame hz
  have T : MsgTieOf (cellAddr tl) D.codes (digList x D rad) (seatOf D x.link) 0
      a.L.check.frame own a.d.st a.d.book rd m :=
    msgTieOf_of (cellAddr tl) D.codes (digList x D rad) (seatOf D x.link) 0
      a.L.check.frame own a.d.st a.d.book rd m seatT h1 C.seat
  obtain ⟨o, ho, hr⟩ := T (.cell t r c) z had hz
  obtain ⟨o', hO⟩ := C.seat (.cell t r c) z had hz
  have hpz : tableOfSeat z = .main := by
    unfold tableOfSeat
    rw [hzm]
    rfl
  rw [hpz] at hr
  rw [ho] at hw
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
    (readAt_some D.codes (digList x D rad) z hO.fits m)
  have e1 : digVal x D rad m (.cell t r c) = some v := by
    show ((seatOf D x.link (.cell t r c)).bind (readAt D.codes (digList x D rad) m)) = _
    rw [hz]
    exact hv
  rw [hv] at hr
  have hr' : v = tabQ own a.d.st a.d.book rd o .main
      (tableIndex (a.d.st.rowBits o .main) (z.row, z.place)) := hr
  have e2 : cellOf a.L (dataQ own a rd) t r c = (dataQ own a rd).cell bn.1 bn.2 r c := by
    unfold cellOf
    rw [C.arr, Array.getD_eq_getD_getElem?, hbn]
    rfl
  rw [e1, e2, hr']
  show _ = some ((dataOf a.L.check.rows a.L.check.frame a.d.st
    (tabQ own a.d.st a.d.book rd)).cell bn.1 bn.2 r c)
  rw [dataOf_cell a.L.check.rows a.L.check.frame a.d.st _ bn.1 bn.2 r c
    (by rw [C.lay]; exact ha) hw (C.laid t r c bn a' o had hbn ha hw), hp]

/-- In the form of the premise hcb. -/
theorem digits_hcb_of (rd : ℕ × ℕ → MsgQ) (m : (digSg x D rad).Msg)
    (h1 : OneReader (ReadMsgOf (cellAddr tl) (seatOf D x.link)) D.codes (digList x D rad) seatT m
      rd)
    (a : Desc.K9.Part) (C : CellOkR x tl D rad seatT own a)
    (hs : ∀ r < 32, ∀ i < tl.bzColumns, (seatOf D x.link (.cell tl.ix.BZ r i)).isSome = true) :
    ∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad m (.cell tl.ix.BZ r i) =
        some (unknownOf a.L (dataQ own a rd) (Sum.inl (tl.ix.BZ, r, i))) :=
  fun r hr i hi => digits_cellRow_of x tl D rad seatT own rd m h1 a C tl.ix.BZ r i
    (Or.inl ⟨r, i, hr, hi, rfl⟩) (hs r hr i hi)

/-- In the form of the premise hcz. -/
theorem digits_hcz_of (rd : ℕ × ℕ → MsgQ) (m : (digSg x D rad).Msg)
    (h1 : OneReader (ReadMsgOf (cellAddr tl) (seatOf D x.link)) D.codes (digList x D rad) seatT m
      rd)
    (a : Desc.K9.Part) (C : CellOkR x tl D rad seatT own a)
    (hs : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      (seatOf D x.link (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i))).isSome = true) :
    ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad m (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf a.L (dataQ own a rd) (Sum.inl (tl.ix.ZZ, p.r0 + r, p.c0 + i))) :=
  fun q hq p hp r hr i hi => digits_cellRow_of x tl D rad seatT own rd m h1 a C tl.ix.ZZ
    (p.r0 + r) (p.c0 + i) (Or.inr ⟨q, p, r, i, hq, hp, hr, hi, rfl⟩) (hs q hq p hp r hr i hi)

/-- **THE DICTIONARY ON CELLS**, at the table's own reader. -/
theorem digits_cellRow (a : Desc.K9.Part) (C : CellOk x tl D rad seatT ms own a)
    (w : Wit Cells Tok MsgT) (t r c : ℕ) (had : cellAddr tl (.cell t r c))
    (hs : (seatOf D x.link (.cell t r c)).isSome = true) :
    digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell t r c) =
      some (cellOf a.L (dataQ own a (seatTab D.codes arr ms w)) t r c) :=
  digits_cellRow_of x tl D rad seatT own (seatTab D.codes arr ms w)
    (msgsOf D.codes (digList x D rad) seatT arr w)
    (oneReader_at _ D.codes arr (digList x D rad) seatT ms w C.mem) a C.r t r c had hs

/-- In the form of the premise hcb. -/
theorem digits_hcb (a : Desc.K9.Part) (C : CellOk x tl D rad seatT ms own a)
    (w : Wit Cells Tok MsgT)
    (hs : ∀ r < 32, ∀ i < tl.bzColumns, (seatOf D x.link (.cell tl.ix.BZ r i)).isSome = true) :
    ∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tl.ix.BZ r i) =
        some (unknownOf a.L (dataQ own a (seatTab D.codes arr ms w)) (Sum.inl (tl.ix.BZ, r, i))) :=
  digits_hcb_of x tl D rad seatT own (seatTab D.codes arr ms w)
    (msgsOf D.codes (digList x D rad) seatT arr w)
    (oneReader_at _ D.codes arr (digList x D rad) seatT ms w C.mem) a C.r hs

/-- In the form of the premise hcz. -/
theorem digits_hcz (a : Desc.K9.Part) (C : CellOk x tl D rad seatT ms own a)
    (w : Wit Cells Tok MsgT)
    (hs : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      (seatOf D x.link (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i))).isSome = true) :
    ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf a.L (dataQ own a (seatTab D.codes arr ms w))
          (Sum.inl (tl.ix.ZZ, p.r0 + r, p.c0 + i))) :=
  digits_hcz_of x tl D rad seatT own (seatTab D.codes arr ms w)
    (msgsOf D.codes (digList x D rad) seatT arr w)
    (oneReader_at _ D.codes arr (digList x D rad) seatT ms w C.mem) a C.r hs

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.whereIs_own
#print axioms VerifiableInference.OnPublicFiles.digits_cellRow_of
#print axioms VerifiableInference.OnPublicFiles.digits_cellRow
#print axioms VerifiableInference.OnPublicFiles.digits_hcb
#print axioms VerifiableInference.OnPublicFiles.digits_hcz
