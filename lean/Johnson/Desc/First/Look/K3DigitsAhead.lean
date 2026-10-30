-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsAhead.lean: the lookup on the digits of a segment's approximate
range proof: THE LOOKUP's READING OF THE DIGITS' CELLS (digMu) IS THE APPROXIMATE RANGE PROOF's
LAW's ONE TABLE OF CELLS (cellsAhead, Johnson/Desc/First/K8/CellsAhead.lean) AT THE
CELLS THAT «the digits are in their tables» READS, AND AT NO OTHER. One structure of premises, one
theorem: a joining. NO SOUNDNESS IS CLAIMED.

Main names.
  DigAheadOk: what digMu_ahead (Johnson/Top/H/Keep/DigitsCellAhead.lean) asks, gathered: of the part
    that segAt? reads off the state: hfr, hlay, harr, hcs · and AT EACH CELL OF THE RANGE: a seat z
    with hz, hfit, hM, hA, hN, hv.
  digMu_cellsAhead: under it, at each cell of the range: digMu … (enOf x.arrays (tl.ix.ZZ, u, col))
    = cellsAhead D.codes arr ms N l (z, s) w tl.ix.ZZ u col.
THE RANGE. μ < tl.NM · u < tl.tau · i < (tl.mats.getD μ {}).m · b < 2 · col := (tl.zzCol μ b 0).getD
0 + i. OUTSIDE IT NOTHING IS SAID: an entry without a seat that fits and the table's 0 may part.
OBJECT. Two readings of one witness.
USER. digitsAt_mgAll's premise hE (Johnson/Desc/Sound/MgAt/K3DigitsAt.lean).
LETTERS. x, tl, D, rad, seatT, arr, ms, N, l; z, s, w.


Compiled with the whole library.
Limits. DigAheadOk is shown at no state.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.DigitsCellAhead
import Johnson.Desc.First.K8.CellsAhead

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

open VerifiableInference.Desc.First (Numbers)

section
variable {P Cells Tok : Type} (x : Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (l : ℕ)

/-- **What the equation asks**, at the state s and the witness w. -/
def DigAheadOk (s : Desc.First.S) (w : Wit Cells Tok MsgT) : Prop :=
  ∃ a, Desc.K9.segAt? s = some a ∧ FrameIs D x.link a.L.check.frame ∧
    a.L.check.rows.layout = D.layout ∧ a.L.arrayOf = D.arrayOf.getD x.link #[] ∧
    a.d.st.codes = D.codes ∧
    ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      ∃ z : Seat, seatOf D x.link (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) = some z ∧
        z.Fits D.codes (digList x D rad) ∧
        (∀ hk : z.msg < (digList x D rad).length, MemAt ms (digList x D rad) seatT ⟨z.msg, hk⟩) ∧
        (∀ bn h, (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
          aheadIn (N.sent l) (N.group l) a bn = some h →
          (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
            laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) =
              true) ∧
        (∀ bn a', (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
          aheadIn (N.sent l) (N.group l) a bn = none → reqArray D.layout bn.1 bn.2 = some a' →
          ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 (N.group l) a.d.st
              a.d.book z o ∧
            laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true) ∧
        digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
            (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) =
          some (digMu x D rad seatT arr w
            (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i)))

/-- **THE TWO READINGS ARE ONE AT THE CELLS OF THE RANGE.** -/
theorem digMu_cellsAhead (z : P) (s : Desc.First.S) (w : Wit Cells Tok MsgT)
    (K : DigAheadOk x tl D rad seatT arr ms N l s w) :
    ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      digMu x D rad seatT arr w (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i)) =
        Desc.First.K8.cellsAhead D.codes arr ms N l (z, s) w tl.ix.ZZ u
          ((tl.zzCol μ b 0).getD 0 + i) := by
  obtain ⟨a, ha, hfr, hlay, harr, hcs, hall⟩ := K
  intro μ hμ u hu i hi b hb
  obtain ⟨zz, hz, hfit, hM, hA, hN, hv⟩ := hall μ hμ u hu i hi b hb
  exact digMu_ahead x D rad seatT arr ms (N.sent l) (N.group l) s a ha hfr hlay harr hcs w _ _ _ zz
    hz hfit hM hA hN hv

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digMu_cellsAhead
