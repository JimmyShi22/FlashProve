-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/NewSeatsConst.lean: code switching: THE NAMED TEST newSeatsB
(Johnson/Top/H0/Tw/K2C/SmpForms.lean: the list of tenants has no repeats and holds the switch's new
members' tenants from place n0 on) ACCEPTS AT THE CONSTANT's OWN LETTERS, AT EACH OF THE 25 WRITTEN
TYPED ROWS: where the constant's parameters are the written values. NO SUB-PROTOCOL IMPORTS THIS
FILE.
  newSeats25B        the test at every row of a list: row number m at the new members' tenants
                     seatNew N m r (K2Caller/SeatsOfN.lean) and n0 := K2.n0At (m + 1)
                     (Johnson/Top/H0/K2Hears/PlaceNums.lean)
  newSeats25_says    its accept, at a row
  newSeats25_full    THE CLOSED FACT: it accepts at the written tenants, numbers and rows: by Lean's
                     kernel
  newSeats25_moved   a negative test: the rows moved by one place: it rejects
  seatNew_congr      seatNew reads of the numbers the letter sent alone
  newSeats_const     THE STATEMENT, at the constant's letters
CALLED BESIDE: AtWritten (K2Ties/WrittenAt.lean) · tenantsFull (K2Caller/PlacesWritten.lean).
LIMITS. The full size alone. AtWritten stands under the first pinned test's accept. That
n0At (m + 1) is the number of messages in the verifier's state in front of the switch is not said
here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.Top.H0.K2Caller.PlacesWritten
import Johnson.Top.H0.K2Caller.SeatsOfN
import Johnson.Top.H0.K2Hears.PlaceNums
import Johnson.Top.H0.Tw.K2C.SmpForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.K2 (newSeatsB n0At)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit seatNew)
open P1Named (tenantsFull)
open P5J (TS)

/-- The test at every row of a list. -/
def newSeats25B (seats : List (ℕ × ℕ)) (N : Numbers) (rows : List SwRow) : Bool :=
  rows.zipIdx.all fun x => newSeatsB seats (seatNew N x.2 x.1) (n0At (x.2 + 1))

theorem newSeats25_says {seats : List (ℕ × ℕ)} {N : Numbers} {rows : List SwRow}
    (h : newSeats25B seats N rows = true) {m : ℕ} {r : SwRow} (hr : rows[m]? = some r) :
    newSeatsB seats (seatNew N m r) (n0At (m + 1)) = true :=
  List.all_eq_true.1 h (r, m) (List.mem_zipIdx_iff_getElem?.2 hr)

set_option maxRecDepth 1000000 in
/-- **The closed fact.** -/
theorem newSeats25_full : newSeats25B tenantsFull P5T.N0Full tableFullLit = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem newSeats25_moved :
    newSeats25B tenantsFull P5T.N0Full (tableFullLit.drop 1) = false := by decide +kernel

theorem seatNew_congr {N N' : Numbers} (hs : N.sent = N'.sent) (m : ℕ) (r : SwRow) :
    seatNew N m r = seatNew N' m r := by
  funext i
  unfold seatNew
  rw [hs]

/-- **The test accepts at the constant's own letters**, at each written typed row. -/
theorem newSeats_const {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) {m : ℕ}
    {r : SwRow} (hr : tableFullLit[m]? = some r) :
    newSeatsB (P5J.At.seats Zp) (seatNew (P5J.At.N Zp cF) m r) (n0At (m + 1)) = true := by
  rw [A.seats, seatNew_congr A.sent]
  exact newSeats25_says newSeats25_full hr

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.newSeats25_says
#print axioms VerifiableInference.Desc.First.K2Ties.newSeats25_full
#print axioms VerifiableInference.Desc.First.K2Ties.newSeats25_moved
#print axioms VerifiableInference.Desc.First.K2Ties.newSeats_const
