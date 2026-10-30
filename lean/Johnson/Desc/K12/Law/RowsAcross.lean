-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.SeatLaws
import Johnson.Top.H0.K2Hands.RowsGround
import Johnson.Top.H0.K2Hears.SentRows
/-
Johnson/Desc/K12/Law/RowsAcross.lean: AN INVARIANT ON THE STORED SAMPLE ROWS CROSSES THE PROXIMITY TEST.
For part 1's induction along the proof file's first chain (Johnson/Top/H0/K2Hands/SampleChain.lean:
RowsInv Q: of every message that has stored sample rows, Q holds at the codes, its shape, its number
and these rows). THE PROXIMITY TEST IS A SENDER, NOT A KEEPER: each code switch in it sends two messages
and admits the sampled one: new stored rows come. So what crosses is the invariant, not «the rows
stand». One induction over our k12_calls (Johnson/Desc/K12/Law/Calls.lean: an accept of the
sub-protocol's decision is a run of the ground's plain calls), step by step with part 1's lemmas on
these calls (Johnson/Top/H0/K2Hands/RowsGround.lean).
BOOK-KEEPING ON THE VERIFIER's STATE. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  AdmitGives Q      THE ONE PREMISE: Q holds of rows that rowsFor has made at the codes, a shape that fits
      them, the message's number, from seeds whose points have at least the cube's bits: what the step
      «admit» of a run says of its rows (Johnson/Desc/K12/Law/CallsDef.lean)
  call_inv | calls_inv   a step | a run keeps RowsInv Q, under AdmitGives Q
  k12_inv           ★★ (proximityTestKind guardedProximityTestParts p).decide t0 rs gs = .ok tE ⇒ RowsInv Q t0.st → RowsInv Q tE.st: NO
      PREMISE ON THE PLACE, THE STATE OR THE VIEW
  admitGives_good   AdmitGives QGood: by part 1's rowsFor_are (Johnson/Top/H0/K2Hears/SentRows.lean)
  k12_good · atFinish_inv | atFinish_good   ★★ at QGood no premise is left; at the first chain's seat, in
      part 1's own form KeepsInv Q (K12.atFinish p)
WHAT IS NOT HERE: AdmitGives QGoodS: of its three clauses on a seed the first (enough coordinates) is in
the step's own word; «the factor is not zero» is Desc.Plain.sendP's own test and «the factor is in
canonical form» leans on the rounds' drawn elements: NEITHER IS SAID BY A RUN OF CALLS: the walk must be
typed anew with the rounds in hand.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.First.K2 (RowsInv QGood SameRows rowsInv_rows KeepsInv Inv)
open _root_.Desc.Plain (rowsFor)

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {ft : Nat}

/-- What a run's step «admit» says of its rows gives Q. -/
def AdmitGives (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) : Prop :=
  ∀ (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed) (ys ys' : List E)
    (rows : Array OnBytes.Row), Blk.shapeOk codes s = true →
    (∀ sd ∈ seeds, (Send.cube codes s).bits ≤ sd.z.length) →
    rowsFor codes s o seeds (List.range s.answers) ys #[] = some (rows, ys') → Q codes s o rows

/-- One step keeps the invariant. -/
theorem call_inv (hA : AdmitGives Q) (d d' : DS) (h : Call ft d d') (hd : RowsInv Q d.st) :
    RowsInv Q d'.st := by
  cases h with
  | newGroup h => exact rowsInv_rows (First.K2.newGroupP_rows _ _ _ _ _ h) hd
  | recv h => exact First.K2.recvP_inv _ _ _ _ _ h hd
  | admit hs hok hz hr h =>
    refine First.K2.admitP_inv _ _ _ _ h hd fun x hx => ?_
    rw [hx] at hs
    obtain rfl := Option.some.inj hs
    exact hA _ _ _ _ _ _ _ hok hz hr
  | join h => exact rowsInv_rows (First.K2.joinP_rows _ _ _ _ _ h) hd
  | addRow h => exact rowsInv_rows (First.K2.addRowP_rows _ _ _ _ h) hd
  | closeLedger h => exact rowsInv_rows (First.K2.closeLedgerP_rows _ _ _ h) hd
  | spend h => exact rowsInv_rows (First.K2.spendAsMaskP_rows _ _ _ h) hd
  | begin h => exact rowsInv_rows (First.K2.beginRunP_rows _ _ _ _ h) hd
  | count t => exact hd
  | cols l => exact hd

/-- A run keeps the invariant. -/
theorem calls_inv (hA : AdmitGives Q) {d d' : DS} (h : Calls ft d d') (hd : RowsInv Q d.st) :
    RowsInv Q d'.st := by
  induction h with
  | nil d => exact hd
  | cons s _ ih => exact ih (call_inv hA _ _ s hd)

/-- ★★ An accept of the proximity test's decision keeps the invariant. -/
theorem k12_inv (hA : AdmitGives Q) (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) (h0 : RowsInv Q t0.st) :
    RowsInv Q tE.st :=
  calls_inv hA (k12_calls p t0 tE rs gs h [] []) h0

/-- The rows that rowsFor makes are the program's Send.form at the seeds. -/
theorem admitGives_good : AdmitGives QGood :=
  fun _ _ _ seeds _ _ _ _ _ hr => ⟨seeds, First.K2.rowsFor_are hr⟩

/-- ★★ -/
theorem k12_good (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) (h0 : RowsInv QGood t0.st) :
    RowsInv QGood tE.st :=
  k12_inv admitGives_good p t0 tE rs gs h h0

/-- ★★ At the first chain's seat, in the induction's own form. -/
theorem atFinish_inv (hA : AdmitGives Q) (p : P12) : KeepsInv Q (K12.atFinish p) := by
  intro s s' rs gs _ hy hg
  have h' : ((enterFinish s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind (leaveFinish s)) = .ok s' := hy
  cases he : enterFinish s with
  | error e => rw [he] at h'; cases h'
  | ok t =>
    rw [he] at h'
    have h2 : ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind (leaveFinish s) = .ok s' := h'
    cases hd : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs with
    | error e => rw [hd] at h2; cases h2
    | ok t' =>
      rw [hd] at h2
      have h3 : leaveFinish s t' = .ok s' := h2
      obtain ⟨o, _, _, _, rfl⟩ := Seat.enterFinish_ok s t he
      obtain rfl := Except.ok.inj h3
      exact k12_inv hA p _ t' rs gs hd hg

/-- ★★ At QGood no premise is left. -/
theorem atFinish_good (p : P12) : KeepsInv QGood (K12.atFinish p) := atFinish_inv admitGives_good p

end H2K.Out

#print axioms H2K.Out.calls_inv
#print axioms H2K.Out.k12_inv
#print axioms H2K.Out.admitGives_good
#print axioms H2K.Out.k12_good
#print axioms H2K.Out.atFinish_inv
#print axioms H2K.Out.atFinish_good
