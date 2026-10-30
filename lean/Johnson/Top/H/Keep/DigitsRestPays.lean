-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/DigitsRestPays.lean: The kind "lookup" (K3), at the lookup on the approximate
range proof's digits: THE THREE PREMISES THAT TIE THE BATCHING's DATA TO THE WITNESS (the cells of
the counts' array, the cells of the digits' array's pieces, the mask row at the slots that the
first four claims of "K8.equations" name), PAID AT THE DATA THAT THE TABLE OF JOINTS READS OFF THE
WITNESS, y := dataQ own a (seatTab D.codes arr ms w), AND AT ANY LINK's CONTEXT L WITH THE PART's
LIST OF ARRAYS. THE CONCLUSION's THREE CONJUNCTS ARE, TO THE LETTER, THE FIELDS cellsB, cellsZ,
masks OF THE STRUCTURE DigitsRest (Johnson/Desc/First/Link/Law/WorthAtFront.lean),
which this file does not import. One statement: a joining of
Johnson/Top/H/Keep/DigitsCell.lean and Johnson/Desc/First/Look/K3DigitsMask.lean.
GENERAL IN THE READER rd.

OBJECT: digVal, digMu at msgsOf of the witness; K8.Four.unknownOf at dataQ.
Used by Johnson/Desc/First/Link/Law/LeftThree.lean.
LETTERS: x, tl, D, rad, seatT, arr, ms, own; a: a part of the verifier's state; L; c: the run's list
  of claims; w.
Compiled with the whole library.

Main names:
  unknownOf_arrays: the data's unknowns read a link's context at its list of arrays alone.
  rest_pays_of: THE END, at y := dataQ own a rd for any reader rd with OneReader at the members that
    hold the read cells and the mask row.
  rest_pays: its instance at rd := seatTab D.codes arr ms w.

Limits. PREMISES: DigOK (public) · CellOk and MaskOk at the part a (shown of no state; CellOk can
hold only where the messages that hold the two arrays are sent) · hB (a public Bool) · hL: L has
a's list of arrays · hc0: each piece's first column is its call's (from PieceOK) · hns4: every slot
that a form of the four names lies below a's ledger's number of slots. THAT THE BATCHING's LAW's
DATA y ARE dataQ own a (seatTab ... w) AT SUCH A PART IS WHOEVER CALLS's.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.DigitsCell
import Johnson.Desc.First.Look.K3DigitsMask
import Johnson.Desc.First.Look.K3DigitsWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params OnBytes.DgP
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (Mem MsgT MsgQ dataQ seatTab msgsOf)
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf oneReader_at)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (cellOf unknownOf)

/-- The data's unknowns read a link's context at its list of arrays alone. -/
theorem unknownOf_arrays {K : Type} [Field K] (L L' : LinkCtx) (y : Desc.K9L.Bound K)
    (h : L.arrayOf = L'.arrayOf) : unknownOf L y = unknownOf L' y := by
  unfold unknownOf cellOf
  rw [h]

/-- Where the messages hold something at an address, the address has a seat. -/
theorem seat_of_digVal {x : Desc.First.Look.Place} {D : Sent} {rad : OracleShape → ℕ}
    {m : (digSg x D rad).Msg} {ad : Addr} {v : Cb.Gl.E} (h : digVal x D rad m ad = some v) :
    (seatOf D x.link ad).isSome = true := by
  have h' : (seatOf D x.link ad).bind (readAt D.codes (digList x D rad) m) = some v := h
  obtain ⟨z, hz, _⟩ := Option.bind_eq_some_iff.1 h'
  rw [hz]
  rfl

section
variable {Cells Tok : Type} {x : Desc.First.Look.Place} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → ℕ} (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (own : List (ℕ × ℕ))

/-- **THE END, at any reader of the witness's tables by seat.** -/
theorem rest_pays_of {set : Params.Setting} {pp : ℕ} (HD : DigOK set x tl D rad pp)
    (rd : ℕ × ℕ → MsgQ) (w : Wit Cells Tok MsgT)
    (hc : OneReader (ReadMsgOf (cellAddr tl) (seatOf D x.link)) D.codes (digList x D rad) seatT
      (msgsOf D.codes (digList x D rad) seatT arr w) rd)
    (hm : OneReader (ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link)) D.codes (digList x D rad)
      seatT (msgsOf D.codes (digList x D rad) seatT arr w) rd)
    (a : Desc.K9.Part) (C : CellOkR x tl D rad seatT own a) (M : MaskOkR x D rad seatT own a)
    (hB : maskB D (digList x D rad) x.link x.arrays.ns = true)
    (L : LinkCtx) (hL : L.arrayOf = a.L.arrayOf)
    (hc0 : ∀ q < 2, ∀ p ∈ piecesL tl q, p.c0 = q * tl.mz) (c : List Desc.Claim)
    (hns4 : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList, s.1 < a.F.ns) :
    (∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tl.ix.BZ r i) =
        some (unknownOf L (dataQ own a rd) (Sum.inl (tl.ix.BZ, r, i)))) ∧
    (∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf L (dataQ own a rd) (Sum.inl (tl.ix.ZZ, p.r0 + r, p.c0 + i)))) ∧
    ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList,
      (dataQ own a rd).mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1) := by
  rw [unknownOf_arrays L a.L _ hL]
  exact ⟨digits_hcb_of x tl D rad seatT own rd _ hc a C fun r hr i hi =>
      seat_of_digVal (dig_cell_bz HD (dig_full HD)
        (msgsOf D.codes (digList x D rad) seatT arr w) hr hi),
    digits_hcz_of x tl D rad seatT own rd _ hc a C fun q hq p hp r hr i hi =>
      seat_of_digVal (dig_cell_zz HD (msgsOf D.codes (digList x D rad) seatT arr w) hq hp
        (hc0 q hq p hp) hr hi),
    fun k hk s hs => digits_maskRow_of x tl D rad seatT arr own hB rd w hm a M s.1
      (hns4 k hk s hs)⟩

/-- **THE END**, at the table's own reader. -/
theorem rest_pays {set : Params.Setting} {pp : ℕ} (HD : DigOK set x tl D rad pp)
    (a : Desc.K9.Part) (C : CellOk x tl D rad seatT ms own a) (M : MaskOk x D rad seatT ms own a)
    (hB : maskB D (digList x D rad) x.link x.arrays.ns = true) (w : Wit Cells Tok MsgT)
    (L : LinkCtx) (hL : L.arrayOf = a.L.arrayOf)
    (hc0 : ∀ q < 2, ∀ p ∈ piecesL tl q, p.c0 = q * tl.mz) (c : List Desc.Claim)
    (hns4 : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList, s.1 < a.F.ns) :
    (∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tl.ix.BZ r i) =
        some (unknownOf L (dataQ own a (seatTab D.codes arr ms w)) (Sum.inl (tl.ix.BZ, r, i)))) ∧
    (∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
          (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (unknownOf L (dataQ own a (seatTab D.codes arr ms w))
          (Sum.inl (tl.ix.ZZ, p.r0 + r, p.c0 + i)))) ∧
    ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList,
      (dataQ own a (seatTab D.codes arr ms w)).mask s.1 =
        digMu x D rad seatT arr w (mkOf x.arrays s.1) :=
  rest_pays_of seatT arr own HD (seatTab D.codes arr ms w) w
    (oneReader_at _ D.codes arr (digList x D rad) seatT ms w C.mem)
    (oneReader_at _ D.codes arr (digList x D rad) seatT ms w M.mem) a C.r M.r hB L hL hc0 c hns4

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.unknownOf_arrays
#print axioms VerifiableInference.OnPublicFiles.rest_pays_of
#print axioms VerifiableInference.OnPublicFiles.rest_pays
