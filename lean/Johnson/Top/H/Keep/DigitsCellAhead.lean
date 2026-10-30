-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/DigitsCellAhead.lean: The kind "lookup" (K3), at the lookup on the approximate
range proof's digits: THE DICTIONARY ON CELLS AT THE DATA THAT READ AHEAD: what the witness's
messages hold at a cell's seat, as the closed caller reads them (digVal), IS THE ENTRY OF THE
FORMS' OWN WORLD OVER dataQA (Johnson/Desc/Sound/FormsAhead.lean):
WHETHER THE ARRAY's MESSAGE IS SENT OR STILL AHEAD. Statements and proofs: the sister of
Johnson/Top/H/Keep/DigitsCell.lean.

OBJECT: digVal, digMu at msgsOf of the witness; worldOwn a [] (dataQA sent own a (seatTab ... w)).
Used by Johnson/Desc/First/Look/K3DigitsAhead.lean.
LETTERS: x, D, rad, seatT, arr, ms, sent, own; a: the part of the verifier's state; w; t, r, c;
  z.
Compiled with the whole library.

Main names:
  aheadIn_array: the array of what is ahead is the layout's.
  cellA_at: THE ARM AHEAD, general in the list: what the messages hold at a seat is cellA there.
  cell_sent: the arm "sent", at one address.
  digits_cellAhead_of: THE END, at one address.
  digMu_ahead_of: as an equation on digMu. ALL FOUR AT ANY READER rd OF THE WITNESS's TABLES BY
    SEAT, under "the two readers are one" (OneReader) at the one member that holds the cell.
  digits_cellAhead, digMu_ahead: the instances at rd := seatTab D.codes arr ms w (oneReader_at under
    hM); the second has the body of cellsAhead (CellsAhead.lean) as its right side.

Limits. ALL PREMISES STAND AT ONE ADDRESS. ON THE STATE: frame, lay, arr, codes. IN THE ARM AHEAD
NOTHING ELSE IS ASKED OF THE STATE: hA: the seat that the plan gives the message is seatT at the
address's member, and the programs' own test on the array's layout accepts at the PLAN's bits. In
the arm "sent": hN: as DigitsCell.lean's CellOk (the live request has the message; the book seats
it; the row fits; the layout's test at the statement's bits). hfit: the seat lies in its table. O:
the reader agrees with the typed message at that member (at seatTab: hM: the table's list of
members has that member). Shown of no state and of no plan.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.DigitsCell
import Johnson.Desc.Sound.FormsAhead
import Johnson.Desc.First.Look.K3DigitsWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params OnBytes.DgP
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (Ahead aheadOf aheadIn rowBitsOf placeBitsOf)
open VerifiableInference.Desc.K9L (dataOf BlockFacts blockFacts)
open VerifiableInference.Desc.Sound (Mem MsgT GQ MsgQ dataQ dataQA cellA worldOwn tabQ seatTab
  msgsOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs MemAt SeatOk ReadMsgOf MsgTieOf msgTieOf_of
  OneReader oneReader_at oracleOfMsg tableOfSeat tableIndex tableIndex_parts dataOf_cell blocks_sum
  laidIn_row_lt)

/-- The array of what is ahead is the layout's. -/
theorem aheadIn_array {sent : ℕ → List (ℕ × ℕ)} {own : List (ℕ × ℕ)} {a : Desc.K9.Part}
    {b : ℕ × String} {h : Ahead} (e : aheadIn sent own a b = some h) :
    reqArray a.L.check.rows.layout b.1 b.2 = some h.A := by
  unfold aheadIn at e
  obtain ⟨e, _⟩ := Option.filter_eq_some_iff.1 e
  unfold aheadOf at e
  split at e
  · obtain ⟨A, hA, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    · exact nomatch e
    · obtain ⟨ms, _, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨M, _, e⟩ := Option.bind_eq_some_iff.1 e
      split at e
      · exact nomatch e
      · obtain ⟨y, _, e⟩ := Option.map_eq_some_iff.1 e
        subst e
        exact hA
  · exact nomatch e

section
variable {Cells Tok : Type}

/-- **THE ARM AHEAD**, general in the list of members. -/
theorem cellA_at (cs : Codes) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (rd : ℕ × ℕ → MsgQ) (m : (Johnson.Pack.sigOf cs l).Msg) (h : Ahead) (z : Seat)
    (O : OneReader (fun n => n = z.msg) cs l seat m rd)
    (hfit : z.Fits cs l) (hzm : z.mask = false)
    (hseat : ∀ hk : z.msg < l.length, h.seat = seat ⟨z.msg, hk⟩)
    (hok : laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf cs h.shape .main) = true)
    (r c : ℕ) (hp : laidPlace h.A.blocks r c = some (z.row, z.place)) :
    readAt cs l m z = some (cellA cs h rd r c) := by
  obtain ⟨hk, hf⟩ := hfit
  have hnm : ¬ z.mask = true := by
    rw [hzm]
    exact Bool.false_ne_true
  rw [if_neg hnm] at hf
  unfold laidMatrixOk at hok
  obtain ⟨hok1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hok
  obtain ⟨hall, hno⟩ := Eq.mp (Bool.and_eq_true _ _) hok1
  have facts : ∀ b ∈ h.A.blocks,
      BlockFacts b (rowBitsOf h.shape .main) (placeBitsOf cs h.shape .main) := by
    intro b hb
    have h1 := List.all_eq_true.1 hall b hb
    obtain ⟨h2, _⟩ := Eq.mp (Bool.and_eq_true _ _) h1
    obtain ⟨h3, _⟩ := Eq.mp (Bool.and_eq_true _ _) h2
    exact blockFacts b _ _ h3
  have hrow : z.row < 2 ^ rowBitsOf h.shape .main := by
    have hp' := hp
    unfold laidPlace at hp'
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hp'
    have h1 := laidIn_row_lt b _ _ (facts b (List.mem_of_find?_eq_some hb)) r c
      (List.find?_some (p := fun b => laidHolds b r c) hb)
    rw [e] at h1
    exact h1
  obtain ⟨t1, t2⟩ := tableIndex_parts (rowBitsOf h.shape .main) (z.row, z.place) hrow
  have e1 : cellA cs h rd r c = rd h.seat false z.row z.place := by
    unfold cellA
    rw [blocks_sum (rowBitsOf h.shape .main) (placeBitsOf cs h.shape .main)
      (fun J => rd h.seat false (J % 2 ^ rowBitsOf h.shape .main)
        (J / 2 ^ rowBitsOf h.shape .main)) r c h.A.blocks facts hno, hp]
    show rd h.seat false
      (tableIndex (rowBitsOf h.shape .main) (z.row, z.place) % 2 ^ rowBitsOf h.shape .main)
      (tableIndex (rowBitsOf h.shape .main) (z.row, z.place) / 2 ^ rowBitsOf h.shape .main) = _
    rw [t1, t2]
  rw [e1, hseat hk]
  unfold readAt
  rw [dif_pos hk, if_neg hnm, finOf_some hf.1, finOf_some hf.2]
  exact congrArg some (O.main ⟨z.msg, hk⟩ rfl ⟨z.row, hf.1⟩ ⟨z.place, hf.2⟩)

variable (x : Desc.First.Look.Place) (D : Sent)
  (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ))

/-- The arm "sent", at one address. -/
theorem cell_sent (rd : ℕ × ℕ → MsgQ) (m : (digSg x D rad).Msg) (a : Desc.K9.Part)
    (hlay : a.L.check.rows.layout = D.layout) (t r c : ℕ) (z : Seat)
    (hz : seatOf D x.link (.cell t r c) = some z)
    (O : OneReader (fun n => n = z.msg) D.codes (digList x D rad) seatT m rd)
    (bn : ℕ × String) (a' : ReqArray) (ha : reqArray D.layout bn.1 bn.2 = some a')
    (hp : laidPlace a'.blocks r c = some (z.row, z.place)) (hzm : z.mask = false) (o : ℕ)
    (hw : a.L.check.frame.whereIs bn.1 a'.message = oracleOfMsg a.L.check.frame 0 z.msg)
    (K : SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o)
    (hok : laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true) :
    readAt D.codes (digList x D rad) m z = some ((dataQ own a rd).cell bn.1 bn.2 r c) := by
  have hK : ∀ k, ReadMsgOf (fun ad => ad = .cell t r c) (seatOf D x.link) k → k = z.msg := by
    intro k hk
    obtain ⟨ad, z', rfl, hz', hm⟩ := hk
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
    exact hm.symm
  have T : MsgTieOf (fun ad => ad = .cell t r c) D.codes (digList x D rad) (seatOf D x.link) 0
      a.L.check.frame own a.d.st a.d.book rd m :=
    msgTieOf_of (fun ad => ad = .cell t r c) D.codes (digList x D rad) (seatOf D x.link) 0
      a.L.check.frame own a.d.st a.d.book rd m seatT
      ⟨fun k hk => O.main k (hK _ hk), fun k hk => O.mask k (hK _ hk)⟩
      (fun ad z' had hz' => by
        subst had
        obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
        exact ⟨o, K⟩)
  obtain ⟨o', ho, hr⟩ := T (.cell t r c) z rfl hz
  obtain rfl : o = o' := Option.some.inj (K.oracle.symm.trans ho)
  have hpz : tableOfSeat z = .main := by
    unfold tableOfSeat
    rw [hzm]
    rfl
  rw [hpz] at hr
  rw [ho] at hw
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (readAt_some D.codes (digList x D rad) z K.fits m)
  rw [hv] at hr ⊢
  have hr' : v = tabQ own a.d.st a.d.book rd o .main
      (tableIndex (a.d.st.rowBits o .main) (z.row, z.place)) := hr
  rw [hr']
  show _ = some ((dataOf a.L.check.rows a.L.check.frame a.d.st
    (tabQ own a.d.st a.d.book rd)).cell bn.1 bn.2 r c)
  rw [dataOf_cell a.L.check.rows a.L.check.frame a.d.st _ bn.1 bn.2 r c
    (by rw [hlay]; exact ha) hw hok, hp]

/-- **THE END, at one address, at any reader of the witness's tables by seat.** -/
theorem digits_cellAhead_of (rd : ℕ × ℕ → MsgQ) (m : (digSg x D rad).Msg) (a : Desc.K9.Part)
    (hfr : FrameIs D x.link a.L.check.frame)
    (hlay : a.L.check.rows.layout = D.layout) (harr : a.L.arrayOf = D.arrayOf.getD x.link #[])
    (hcs : a.d.st.codes = D.codes) (t r c : ℕ) (z : Seat)
    (hz : seatOf D x.link (.cell t r c) = some z) (hfit : z.Fits D.codes (digList x D rad))
    (O : OneReader (fun n => n = z.msg) D.codes (digList x D rad) seatT m rd)
    (hA : ∀ bn h, (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = some h →
      (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) = true)
    (hN : ∀ bn a', (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = none →
      reqArray D.layout bn.1 bn.2 = some a' →
      ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o ∧
        laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true) :
    digVal x D rad m (.cell t r c) = some ((worldOwn a [] (dataQA sent own a rd)).entry t r c) := by
  obtain ⟨bn, a', hbn, ha, hp, hzm, hw⟩ := whereIs_own hfr hz
  have e1 : digVal x D rad m (.cell t r c) = readAt D.codes (digList x D rad) m z := by
    show ((seatOf D x.link (.cell t r c)).bind (readAt D.codes (digList x D rad) m)) = _
    rw [hz]
    rfl
  have e2 : (worldOwn a [] (dataQA sent own a rd)).entry t r c =
      (dataQA sent own a rd).cell bn.1 bn.2 r c := by
    show (match a.L.arrayOf[t]? with
      | some b => (dataQA sent own a rd).cell b.1 b.2 r c
      | none => 0) = _
    rw [harr, hbn]
  rw [e1, e2]
  show _ = some (match aheadIn sent own a (bn.1, bn.2) with
    | some h => cellA a.d.st.codes h rd r c
    | none => (dataQ own a rd).cell bn.1 bn.2 r c)
  cases e : aheadIn sent own a (bn.1, bn.2) with
  | some h =>
    obtain ⟨h1, h2⟩ := hA bn h hbn e
    have hAa : h.A = a' := by
      have h3 := aheadIn_array e
      rw [hlay] at h3
      exact Option.some.inj (h3.symm.trans ha)
    show _ = some (cellA a.d.st.codes h rd r c)
    rw [hcs]
    exact cellA_at D.codes (digList x D rad) seatT rd m h z O hfit hzm h1 h2 r c
      (by rw [hAa]; exact hp)
  | none =>
    obtain ⟨o, K, hok⟩ := hN bn a' hbn e ha
    exact cell_sent x D rad seatT own rd m a hlay t r c z hz O bn a' ha hp hzm o hw K hok

/-- **THE END, at one address**, at the table's own reader. -/
theorem digits_cellAhead (a : Desc.K9.Part) (hfr : FrameIs D x.link a.L.check.frame)
    (hlay : a.L.check.rows.layout = D.layout) (harr : a.L.arrayOf = D.arrayOf.getD x.link #[])
    (hcs : a.d.st.codes = D.codes) (w : Wit Cells Tok MsgT) (t r c : ℕ) (z : Seat)
    (hz : seatOf D x.link (.cell t r c) = some z) (hfit : z.Fits D.codes (digList x D rad))
    (hM : ∀ hk : z.msg < (digList x D rad).length, MemAt ms (digList x D rad) seatT ⟨z.msg, hk⟩)
    (hA : ∀ bn h, (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = some h →
      (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) = true)
    (hN : ∀ bn a', (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = none →
      reqArray D.layout bn.1 bn.2 = some a' →
      ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o ∧
        laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true) :
    digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell t r c) =
      some ((worldOwn a [] (dataQA sent own a (seatTab D.codes arr ms w))).entry t r c) :=
  digits_cellAhead_of x D rad seatT sent own (seatTab D.codes arr ms w)
    (msgsOf D.codes (digList x D rad) seatT arr w) a hfr hlay harr hcs t r c z hz hfit
    (oneReader_at (fun n => n = z.msg) D.codes arr (digList x D rad) seatT ms w fun k hkk => by
      have hk' : z.msg < (digList x D rad).length := by
        rw [← hkk]
        exact k.2
      have e : k = ⟨z.msg, hk'⟩ := Fin.ext hkk
      rw [e]
      exact hM hk')
    hA hN

/-- **As an equation on the caller's reading, at any reader.** hv: dig_cell_bz,
dig_cell_zz (Johnson/Desc/First/Look/K3DigRows.lean) under DigOK. -/
theorem digMu_ahead_of (rd : ℕ × ℕ → MsgQ) (s : Desc.First.S) (a : Desc.K9.Part)
    (ha : Desc.K9.segAt? s = some a) (hfr : FrameIs D x.link a.L.check.frame)
    (hlay : a.L.check.rows.layout = D.layout) (harr : a.L.arrayOf = D.arrayOf.getD x.link #[])
    (hcs : a.d.st.codes = D.codes) (w : Wit Cells Tok MsgT) (t r c : ℕ) (z : Seat)
    (hz : seatOf D x.link (.cell t r c) = some z) (hfit : z.Fits D.codes (digList x D rad))
    (O : OneReader (fun n => n = z.msg) D.codes (digList x D rad) seatT
      (msgsOf D.codes (digList x D rad) seatT arr w) rd)
    (hA : ∀ bn h, (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = some h →
      (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) = true)
    (hN : ∀ bn a', (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = none →
      reqArray D.layout bn.1 bn.2 = some a' →
      ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o ∧
        laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true)
    (hv : digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell t r c) =
      some (digMu x D rad seatT arr w (enOf x.arrays (t, r, c)))) :
    digMu x D rad seatT arr w (enOf x.arrays (t, r, c)) =
      (match Desc.K9.segAt? s with
        | some p => (worldOwn p [] (dataQA sent own p rd)).entry t r c
        | none => 0) := by
  rw [ha]
  exact Option.some.inj (hv.symm.trans (digits_cellAhead_of x D rad seatT sent own rd _ a hfr hlay
    harr hcs t r c z hz hfit O hA hN))

/-- **At the table's own reader**: THE RIGHT SIDE IS, SIGN FOR SIGN, THE BODY OF
cellsAhead D.codes arr ms N m (z, s) w t r c at sent := N.sent m, own := N.group m. -/
theorem digMu_ahead (s : Desc.First.S) (a : Desc.K9.Part) (ha : Desc.K9.segAt? s = some a)
    (hfr : FrameIs D x.link a.L.check.frame)
    (hlay : a.L.check.rows.layout = D.layout) (harr : a.L.arrayOf = D.arrayOf.getD x.link #[])
    (hcs : a.d.st.codes = D.codes) (w : Wit Cells Tok MsgT) (t r c : ℕ) (z : Seat)
    (hz : seatOf D x.link (.cell t r c) = some z) (hfit : z.Fits D.codes (digList x D rad))
    (hM : ∀ hk : z.msg < (digList x D rad).length, MemAt ms (digList x D rad) seatT ⟨z.msg, hk⟩)
    (hA : ∀ bn h, (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = some h →
      (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) = true)
    (hN : ∀ bn a', (D.arrayOf.getD x.link #[])[t]? = some bn → aheadIn sent own a bn = none →
      reqArray D.layout bn.1 bn.2 = some a' →
      ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 own a.d.st a.d.book z o ∧
        laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true)
    (hv : digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell t r c) =
      some (digMu x D rad seatT arr w (enOf x.arrays (t, r, c)))) :
    digMu x D rad seatT arr w (enOf x.arrays (t, r, c)) =
      (match Desc.K9.segAt? s with
        | some p => (worldOwn p [] (dataQA sent own p (seatTab D.codes arr ms w))).entry t r c
        | none => 0) :=
  digMu_ahead_of x D rad seatT arr sent own (seatTab D.codes arr ms w) s a ha hfr hlay harr hcs w
    t r c z hz hfit
    (oneReader_at (fun n => n = z.msg) D.codes arr (digList x D rad) seatT ms w fun k hkk => by
      have hk' : z.msg < (digList x D rad).length := by
        rw [← hkk]
        exact k.2
      have e : k = ⟨z.msg, hk'⟩ := Fin.ext hkk
      rw [e]
      exact hM hk')
    hA hN hv

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digMu_ahead
#print axioms VerifiableInference.OnPublicFiles.aheadIn_array
#print axioms VerifiableInference.OnPublicFiles.cellA_at
#print axioms VerifiableInference.OnPublicFiles.cell_sent
#print axioms VerifiableInference.OnPublicFiles.digits_cellAhead_of
#print axioms VerifiableInference.OnPublicFiles.digits_cellAhead
#print axioms VerifiableInference.OnPublicFiles.digMu_ahead_of
