-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/DigitsWritten.lean: the kind "the code switch" (K2): the light
test on a filling (`lightBy`, LightWritten.lean of this folder) at the digits' messages, put to
Lean's kernel at the written plan. Public data alone: codes, shapes, the layout, places, the table
of steps, the declared rounds' entries. Definitions with code; a tie by unfolding; closed facts by
`decide +kernel`, with controls. No head, no state, no prover.

What the digits' filling lays (`K1.digitsFill`, Honest/K1/LotFill.lean) hangs on the seats of the
array "BZ" (`seatsOf`, Johnson/HonestTrace/SeatOf.lean) and on the sizes that two lists of values
state. The seats as a closed term are other authors': `seatsW`
(Johnson/HonestTrace/U3Fit/SeatsAtHead.lean). This file asks the kernel about them at "BZ", and lays
a stand-in for the sizes.

  `rngBy`, `rngIn_by`   the body of `rngIn` (Johnson/HonestTrace/BZVals.lean) a second time, as a
                    function of the declared rounds' entries, which are all that it reads of a
                    round; the tie, with no hypothesis
  `seatsBZW`        `seatsW` at "BZ"
  `valsOf`, `onesVals`, `digitsOnes`, `digitsOnesW`   the stand-in: a filling at given seats whose
                    values state one size for the names of a set, at every segment; at `onesVals`:
                    (1, 1) for "BZ" and for "ZZ"
  `seatsBZW_all`    the written seats are 25, one for each segment from 0 to 24, in order
  `seats_can_lack`  two controls: no seat of a name that no array bears; none without places
  `rngW`            `rngBy` returns at each of the 25 segments
  `rngW_can_fail`, `rngW_moved`   controls: at segment 25 it does not; with the entries moved by one
                    it returns at none of the 25: so the round's name is tested
  `digitsW`         the light test says yes at the stand-in, at all written segments
  `digitsW_empty`, `digitsW_no_bz`, `digitsW_no_zz`, `digitsW_no_size`   controls: at a filling
                    that lays nothing, with either name struck, with no row, with no column: no
  `mineDigitsW`, `digitsW_asks`   the addresses that the digits' share asks, written; at the first
                    segment alone the filling that lays nothing fails there
  `linksW_pos`      each written place stands at a link from 1 on: by reading, with the line above
                    and `addrs_written`, the share asks something at each written place: no
                    statement here says so

Limits. The second text is held to the first by the tie, not by the eye. The stand-in is no filling
that anybody sends: it serves a comparison (DigitsLightAtHead.lean of this folder). That the written
terms are any public files' is another file's matter. Each closed fact is one evaluation by Lean's
kernel, with two options raised (maxRecDepth, maxHeartbeats). One instance, a default table of
scales, is switched off, as in the files beneath. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LightWritten
import Johnson.Desc.ProofFile.Honest.K1.LotFill
import Johnson.HonestTrace.U3Fit.SeatsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Seat pairOf mineOf rngIn)
open OnBytes.HonestTrace.U3.Fit (seatsBy seatsW)
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2 layoutFull)
open Johnson.AtFull.Desc (spotsWritten)
open H2K5.Row (roundsBy cutPairsW)

/-! ## 1 A second text -/

/-- The body of `rngIn`, off the declared rounds' entries. -/
def rngBy (before : String → Option Nat) (E : List Fmt.Entry) (sps : List Spot) (seg : Nat) :
    Option (Nat × Nat) := do
  let sp ← sps.find? fun sp => sp.place.link == some seg && sp.place.kind == .K8
  let c ← sp.cuts.head?
  let n ← before c.look
  let e ← E[n]?
  if e.name == "RNG" then some (n, e.trits) else none

/-- The first text is the second at the rounds' entries. -/
theorem rngIn_by (before : String → Option Nat) (D : List Fmt.DeclaredRound) (sps : List Spot)
    (seg : Nat) : rngIn before D sps seg = rngBy before (D.map (·.entry)) sps seg := by
  have key : ∀ n : Nat, (do
      let d ← D[n]?
      if d.entry.name == "RNG" then some (n, d.entry.trits) else none : Option (Nat × Nat)) =
      (do
        let e ← (D.map (·.entry))[n]?
        if e.name == "RNG" then some (n, e.trits) else none) := by
    intro n
    rw [List.getElem?_map]
    cases D[n]? <;> rfl
  unfold rngIn rngBy
  simp only [key]

/-! ## 2 The written terms -/

/-- The seats of "BZ", closed. -/
def seatsBZW : List Seat := seatsW "BZ"

/-- Values that state the size z for the names that `has` accepts, at every segment. -/
def valsOf (z : Nat × Nat) (has : String → Bool) : ArrayVals :=
  { size := fun _ name => if has name then some z else none
    val := fun _ _ _ _ _ _ => .inl (OnBytes.Slice.toF 0) }

/-- The stand-in's values: one row and one column, for "BZ" and for "ZZ". -/
def onesVals : ArrayVals := valsOf (1, 1) fun name => name == "BZ" || name == "ZZ"

/-- **The stand-in**: a filling at the seats' messages. -/
def digitsOnes (codes : OnBytes.Codes) (shape : ReqShape) (lay : ReqLayout) (seats : List Seat)
    (V : ArrayVals) : RowData :=
  laidData codes shape lay (pairOf seats) (fun _ => 0) V

/-- The addresses that the digits' share of the light test asks (`mineDigits`,
LightByAddress.lean of this folder), at the written terms. -/
def mineDigitsW (a : MsgAddr) : Bool :=
  !mineSwitchW a && !(a.sender == K1.firstAddr) && mineOf seatsBZW a

/-- The stand-in at the written plan. -/
def digitsOnesW (V : ArrayVals) : RowData :=
  digitsOnes proofSizedFull.codes proofSizedFull.request layoutFull seatsBZW V

/-! ## 3 By Lean's kernel -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written seats: one for each segment from 0 to 24, in order.** -/
theorem seatsBZW_all : (seatsBZW.map (·.seg) == List.range 25) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Two controls: of a name that no array bears, and with no places, there is no seat. -/
theorem seats_can_lack :
    ((seatsW "BY").isEmpty &&
      (seatsBy (roundsBy cutPairsW) [] codesFull2 proofSizedFull.request layoutFull
        "BZ").isEmpty) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The round "RNG" is found at each of the 25 segments.** -/
theorem rngW : ((List.range 25).all fun l =>
    (rngBy (roundsBy cutPairsW) P5T.esFull.1 spotsWritten l).isSome) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at segment 25 nothing is found. -/
theorem rngW_can_fail :
    (rngBy (roundsBy cutPairsW) P5T.esFull.1 spotsWritten 25).isSome = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control that reaches the test on the round's name: with the entries moved by one, nothing is
found at any of the 25 segments. -/
theorem rngW_moved : ((List.range 25).any fun l =>
    (rngBy (roundsBy cutPairsW) (P5T.esFull.1.drop 1) spotsWritten l).isSome) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The light test at the stand-in, at all written segments.** The stand-in has values under two
names alone: so each array that the layout lays into a seat's message is called "BZ" or "ZZ". -/
theorem digitsW :
    lightBy (digitsOnesW onesVals) (mineOf seatsBZW) layoutFull addrsW segsW = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: the filling that lays nothing is refused: so the test did meet a seat, and an array
that the layout puts in that seat's message. -/
theorem digitsW_empty :
    lightBy RowData.empty (mineOf seatsBZW) layoutFull addrsW segsW = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: without "BZ" it says no. -/
theorem digitsW_no_bz :
    lightBy (digitsOnesW (valsOf (1, 1) fun name => name == "ZZ")) (mineOf seatsBZW) layoutFull
      addrsW segsW = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: without "ZZ" it says no. -/
theorem digitsW_no_zz :
    lightBy (digitsOnesW (valsOf (1, 1) fun name => name == "BZ")) (mineOf seatsBZW) layoutFull
      addrsW segsW = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Two controls: with no row, and with no column, it says no: so that both arrays have a row and a
column is spent. -/
theorem digitsW_no_size :
    (lightBy (digitsOnesW (valsOf (0, 1) fun name => name == "BZ" || name == "ZZ"))
        (mineOf seatsBZW) layoutFull addrsW segsW ||
      lightBy (digitsOnesW (valsOf (1, 0) fun name => name == "BZ" || name == "ZZ"))
        (mineOf seatsBZW) layoutFull addrsW segsW) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control at the addresses that the digits' share asks, at the first segment alone: at the
filling that lays nothing the test says no. So that share asks something at every beginning of the
written list of segments that is not empty. -/
theorem digitsW_asks :
    lightBy RowData.empty mineDigitsW layoutFull addrsW (segsW.take 1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Each written place stands at a link from 1 on: so the segments in front of it are not none. The
second half is a control: not each stands at a link from 2 on. -/
theorem linksW_pos : ((placesW.all fun p => decide (1 ≤ p.link)) &&
    !(placesW.all fun p => decide (2 ≤ p.link))) = true := by decide +kernel

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.rngBy
#print axioms ProofFile.Honest.K2.Law.rngIn_by
#print axioms ProofFile.Honest.K2.Law.seatsBZW
#print axioms ProofFile.Honest.K2.Law.valsOf
#print axioms ProofFile.Honest.K2.Law.onesVals
#print axioms ProofFile.Honest.K2.Law.digitsOnes
#print axioms ProofFile.Honest.K2.Law.mineDigitsW
#print axioms ProofFile.Honest.K2.Law.digitsOnesW
#print axioms ProofFile.Honest.K2.Law.seatsBZW_all
#print axioms ProofFile.Honest.K2.Law.seats_can_lack
#print axioms ProofFile.Honest.K2.Law.rngW
#print axioms ProofFile.Honest.K2.Law.rngW_can_fail
#print axioms ProofFile.Honest.K2.Law.rngW_moved
#print axioms ProofFile.Honest.K2.Law.digitsW
#print axioms ProofFile.Honest.K2.Law.digitsW_empty
#print axioms ProofFile.Honest.K2.Law.digitsW_no_bz
#print axioms ProofFile.Honest.K2.Law.digitsW_no_zz
#print axioms ProofFile.Honest.K2.Law.digitsW_no_size
#print axioms ProofFile.Honest.K2.Law.digitsW_asks
#print axioms ProofFile.Honest.K2.Law.linksW_pos
