-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexKeyWritten.lean: THE NUMBERS AT WHICH THE KIND's SECOND
LOT AND THE INDEX MASKS' SENDER MEET, AT THE FULL SIZE: CLOSED FACTS ON WRITTEN PUBLIC DATA, BY
LEAN's KERNEL, AND THEIR CARRYING TO THE LIBRARY's HEAD BY CALLS. PUBLIC DATA ALONE: a sending's
numbers, which tables ride, a list of shapes. One definition (a test). Lemmas; none of the library's
goals.

  `atIndexKey` P ride   A PUBLIC TEST on a sending's numbers and its rides: there are more than four
                        messages · the table of message 4 does not ride · message 4 has one mask row
                        · its mask code's message length is 256 · the entries of its mask rows begin
                        at number 8647 of the part's own elements of the extension field
                        (`K1.maskStart`, Honest/K1/MaskLaw.lean) · the place is ⟨1, some 0, 1, K1⟩
  `indexKeyW`           its yes at the opening's written numbers `parGF`
                        (Johnson/Desc/K1/Law/TiesWritten.lean) and the ride that the opening's job
                        has (`K1.rideOf`, `K1.firstFold`, Honest/K1/PlaceJob.lean) at the written
                        `qFull`
  `indexKeyW_can_fail`  A CONTROL THAT SAYS NO: at the same numbers with no table riding: the start
                        is then another: the letter ride is spent
  `atIndexKey_gives`    the six facts out of a yes
  `indexRowsW`          member number 4 of the written list of shapes `mW`
                        (Johnson/Road/K4/K4PinsSends.lean) has one mask row
  `par_at_head`         under the head and the opening: the opening's numbers at the description's
                        own ground are the written ones
  `fold_at_head`        the like of the opening's fold (by `firstFold_congr`)
  `atIndexKey_at_head`  so the test says yes there
  `indexRows_at_head`   under the head: `k4IndexRows` Zp (Honest/K4/Lot/IndexNum.lean) is 1
  `indexNum_at_head`    under the head and the opening: `k4IndexNum` Zp is the witness's number of
                        the message at the table's seat N.index. CALLED BY NOTHING IN THIS FOLDER:
                        it is for whoever joins the lot with the sender's own lot at that number

By. `K1.eG_atAll`, `K1.index_atAll` (Johnson/Desc/K1/Law/TiesAtAll.lean) · `K1.pin1_atAll`
(PinsAtHead.lean there) · `K13.Law.likeFull_in_scope` (Johnson/HB/LLHARD/PlanInScope.lean) ·
`written_of_head` (Johnson/Road/K4/K4HeadWritten.lean), `msgs_sorted` (K4PinsSends.lean).
`K1.firstFold` reads of its argument the request's shape alone, by its text and `K1.frame₀`'s
(Johnson/Desc/K1/First.lean).

IT STANDS OVER TWO OTHER GROUPS OF AUTHORS' FILES THAT ARE NOT IN THIS LIBRARY:
Honest/K1/MaskLaw.lean and PlaceJob.lean; Honest/K4/Lot/IndexNum.lean.

Limits. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. THREE CLOSED FACTS BY EVALUATION IN
LEAN's KERNEL. The head and the opening are premises. Which message and which number: never what
stands in a message. Nothing on any property.
-/
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PinsSends
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF qFull LikeFull)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Road.K4 (mW msgs_sorted written_of_head)
open ProofFile.Honest.K1 (Ride)
open ProofFile.Honest.K4.Lot (k4IndexRows k4IndexNum)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: six facts on a sending's numbers and its rides, at message 4. -/
def atIndexKey (P : K1.Par) (ride : Nat → Option Ride) : Bool :=
  decide (4 < P.sent.size) && (ride 4).isNone && (shapeAt P 4).maskRows == 1 &&
    (P.codes.mask.getD (shapeAt P 4).maskCode default).ell == 256 &&
    ProofFile.Honest.K1.maskStart P ride 4 == 8647 && P.place == ⟨1, some 0, 1, .K1⟩

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written numbers and the opening's own ride.** -/
theorem indexKeyW : atIndexKey parGF (K1.rideOf (K1.firstFold qFull)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A control: with no table riding the test says no.** -/
theorem indexKeyW_can_fail : atIndexKey parGF (fun _ => none) = false := by decide +kernel

/-- **What the test's yes gives.** -/
theorem atIndexKey_gives {P : K1.Par} {ride : Nat → Option Ride} (h : atIndexKey P ride = true) :
    4 < P.sent.size ∧ ride 4 = none ∧ (shapeAt P 4).maskRows = 1 ∧
      (P.codes.mask.getD (shapeAt P 4).maskCode default).ell = 256 ∧
      ProofFile.Honest.K1.maskStart P ride 4 = 8647 ∧ P.place = ⟨1, some 0, 1, .K1⟩ := by
  unfold atIndexKey at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

set_option maxRecDepth 1000000 in
/-- Member number 4 of the written list of shapes has one mask row. -/
theorem indexRowsW : ((mW[4]?).map (·.maskRows)).getD 0 = 1 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- Under the head and the opening the opening's numbers are the written ones. -/
theorem par_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    K1.firstPar Bs.G₀.first (K1.gpOf Zp) = parGF :=
  K1.eG_atAll h O (K1.pin1_atAll h)

/-- The opening's fold reads the request's shape alone. -/
theorem firstFold_congr {q q' : OnBytes.Params.First} (e : q.shape = q'.shape) :
    K1.firstFold q = K1.firstFold q' := by
  unfold K1.firstFold K1.frame₀
  rw [e]

/-- Under the head and the opening the opening's fold is the written one. -/
theorem fold_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    K1.firstFold Bs.G₀.first = K1.firstFold qFull := by
  have hF : LikeFull Bs.G₀.first := by
    rw [O.first]
    exact K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)
  exact firstFold_congr hF.shape

/-- **Under the head and the opening the test says yes at the description's own ground.** -/
theorem atIndexKey_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    atIndexKey (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first)) =
      true := by
  rw [par_at_head h O, fold_at_head h O]
  exact indexKeyW

/-- **Under the head the index masks' message has one mask row, in the lot's own term.** -/
theorem indexRows_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : k4IndexRows Zp = 1 := by
  have e : msgsOfChain Zp.made.proof.1 = mW := by
    rw [(written_of_head h.toAtMg).proof]
    exact msgs_sorted
  unfold k4IndexRows
  rw [e]
  exact indexRowsW

/-- **The lot's number is the witness's number of the message at the table's seat N.index.** -/
theorem indexNum_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    k4IndexNum Zp = P5J.At.arr Zp (P5J.At.N Zp cF).index.1 (P5J.At.N Zp cF).index.2 := by
  rw [show (P5J.At.N Zp cF).index = (1, 0) from K1.index_atAll h O (K1.pin1_atAll h)]
  rfl

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.atIndexKey
#print axioms ProofFile.Honest.K11.indexKeyW
#print axioms ProofFile.Honest.K11.indexKeyW_can_fail
#print axioms ProofFile.Honest.K11.atIndexKey_gives
#print axioms ProofFile.Honest.K11.indexRowsW
#print axioms ProofFile.Honest.K11.par_at_head
#print axioms ProofFile.Honest.K11.firstFold_congr
#print axioms ProofFile.Honest.K11.fold_at_head
#print axioms ProofFile.Honest.K11.atIndexKey_at_head
#print axioms ProofFile.Honest.K11.indexRows_at_head
#print axioms ProofFile.Honest.K11.indexNum_at_head
