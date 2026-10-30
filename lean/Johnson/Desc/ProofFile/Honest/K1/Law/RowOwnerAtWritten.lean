-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RowOwnerAtWritten.lean: THE SHARED "SENDING" (the kind K1) AND
THE MAKER OF THE BOOK OF COINS: THE MAKER's SEARCH FOR THE FIRST SEGMENT's MASK ROW (ownerOf,
Johnson/Desc/ProofFile/Honest/BookEntries.lean, at "link 0, moment 0" and isMaskRowMsg), AT THE
LIBRARY's WRITTEN DATA: ITS OWNER IS THE OPENING's SENDER; ITS START AMONG THAT PART's COINS OF THE
EXTENSION FIELD IS OUR maskStart (Johnson/Desc/ProofFile/Honest/K1/MaskLaw.lean) AT MESSAGE NUMBER
0; ITS SEARCH PICKS NUMBER 0. THE SISTER OF
Johnson/Desc/ProofFile/Honest/K1/Law/OwnerAtWritten.lean (the index-mask message, number 4). PUBLIC
DATA ALONE: where a run of coins begins, never what stands in it. Eleven theorems; NO DEFINITION.
NO PROPERTY IS
CLAIMED.

THE WRITTEN DATA: as in OwnerAtWritten.lean's head: the blocks that the written cut and the written
declared rounds of the first chain spell · the first chain's written sendings · the second chain's
written declared rounds · the opening's written plan K1.parGF with the ride rideOf (firstFold
K1.qFull).

HOW IT IS MADE. (A1) would be an
instance, and only «ownerOf's base is that maskStart at the written sending» stays closed-number
work: rowBaseW IS THAT CLOSED-NUMBER WORK; rowOwnerW IS AN INSTANCE OF maskStart_book_e
(Johnson/Desc/ProofFile/Honest/K1/Law/MaskStartIsBook.lean), at hf := fits_first_written, ht :=
tiedW.

  - tiedW   THE TIE OF THE RIDE at the written plan, at the maker's k = 8.
  - firstSendingW   the first written sending's messages and the chain's codes ARE the plan's.
  - rowPickW   (A2) the first written sending is "link 0, moment 0"; the first of its messages that
                  meets isMaskRowMsg is number 0.
  - rowBaseW   what ownerOf returns has the owner ⟨K1.parGF.place, 0⟩ and, as its base, the maker's
                  maskStart at the plan's codes, k = 8, the plan's messages, number 0. THE NUMERAL
                  8 IS IDLE THERE: at number 0 the maker's maskStart reads no message in front, and
                  of message 0 what k does not enter: any k gives the same. WHAT TRIES k: tiedW,
                  and OwnerAtWritten.lean's start at message 4, behind the riding message's 2 k +
                  1.
  - rowOwnerW   (A1) so its base's count of the extension field is OUR maskStart at number 0.
  - rowOwnerW_bites   (A3) A NEGATIVE TEST: of the five messages NUMBER 0 ALONE has that start.
  - rowFreeW   (A5) the maker's free entries, 8191, are fewer than the mask rows' entries of number
                  0, 8192.
  - rowNextW   A NUMBER THAT IS NOT 0: the next message's coins of the extension field begin at
                  8411 = 0 + 8192 + 219.
  - rowBaseW_bent   THE EVALUATION CAN FAIL: at number 1 for number 0 on the right the test
                  rejects.
  - rowBaseW_bent_owner   THE OWNER BENT (in rowBaseW's twin now only the number is):
                  with part 1 of
                  the opening's place, or with the place ⟨1, some 0, 4, .K1⟩, for the owner on the
                  right, the test rejects.
  - rowOwnerW_head   UNDER h (the library's head: A HYPOTHESIS), O: the same left side; on the
                  right the plan and the ride at the description's own ground.

NOT LAID HERE: (A6) ALL FIVE STARTS, 0 · 8411 ·
8411 · 8411 · 8647, WITH EACH MESSAGE's FOUR NUMBERS AND ITS RIDE, at
(K1.parGF, rideOf (firstFold K1.qFull))
(K1.parGF := firstPar qFull gpFull,
Johnson/Desc/K1/Law/TiesWritten.lean)
· (A4) no table rides at number 0: our rides_first_written
(Johnson/Desc/ProofFile/Honest/K1/Law/RideAtPlans.lean).

Limits. (A1) IS AN EQUATION "0 = 0" BETWEEN TWO COUNTS THAT BOTH BEGIN AT 0: BY ITSELF IT TELLS
LITTLE (the reviewer's word): the five starts, rowOwnerW_bites, rowNextW and the general law beside
it carry the weight. IT IS A PREMISE's FORECAST, NOT ITS PAYMENT: that the blocks of the head's
description, its rounds and the maker's sendings ARE the written ones is not said here. THE FULL
SIZE ALONE. Evaluations in Lean's kernel (decide +kernel): no compiled code. It stands over files
that are on no row. Nothing on the book's entries, on a spender, or on what any coin is. Nothing on
any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.OwnerAtWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.MaskStartIsBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)

/-- **THE TIE OF THE RIDE, AT THE WRITTEN PLAN**, at the maker's k = 8. -/
theorem tiedW : ∀ j, j < parGF.sent.size →
    (rideOf (firstFold K1.qFull) j).map (·.k) =
      if isFresh (parGF.sent.getD j default) then some 8 else none := by
  have h : ((List.range parGF.sent.size).all fun j =>
      decide ((rideOf (firstFold K1.qFull) j).map (·.k) =
        if isFresh (parGF.sent.getD j default) then some 8 else none)) = true := by
    decide +kernel
  intro j hj
  exact of_decide_eq_true (List.all_eq_true.1 h j (List.mem_range.2 hj))

/-- The first written sending's messages, and the chain's codes, are the plan's. -/
theorem firstSendingW : Johnson.G.proofSendsFull.1.sends.head?.map (·.sent) =
      some parGF.sent.toList ∧ Johnson.G.proofSendsFull.1.codes = parGF.codes := by
  decide +kernel

/-- (A2) The maker's search picks message number 0 of the first written sending. -/
theorem rowPickW : (Johnson.G.proofSendsFull.1.sends.head?.map fun x =>
    (x.label, x.sent.findIdx isMaskRowMsg)) = some ("link 0, moment 0", 0) := by
  decide +kernel

/-- **THE CLOSED-NUMBER WORK: ownerOf's BASE IS THE MAKER's maskStart AT THE WRITTEN SENDING.** -/
theorem rowBaseW : (ownerOf maskRowRun
    (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
      P2Law.ProofPlan.declProofFull.1)
    Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
    isMaskRowMsg).map (fun m => (m.owner, m.base)) =
    (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0).map
      fun st => ((⟨parGF.place, 0⟩ : Addr), st) := by
  decide +kernel

/-- **(A1) THE MAKER's MASK ROW AT THE WRITTEN DATA**: its owner; its start among the coins of E:
an instance of maskStart_book_e. -/
theorem rowOwnerW : (ownerOf maskRowRun
    (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
      P2Law.ProofPlan.declProofFull.1)
    Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
    isMaskRowMsg).map (fun m => (m.owner, m.base.e)) =
    some ((⟨parGF.place, 0⟩ : Addr), maskStart parGF (rideOf (firstFold K1.qFull)) 0) := by
  have q := maskStart_book_e parGF (rideOf (firstFold K1.qFull)) 8 fits_first_written tiedW
    (j := 0) (by decide +kernel)
  have e : (ownerOf maskRowRun
      (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
        P2Law.ProofPlan.declProofFull.1)
      Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
      isMaskRowMsg).map (fun m => (m.owner, m.base.e)) =
      ((ownerOf maskRowRun
          (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
            P2Law.ProofPlan.declProofFull.1)
          Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
          isMaskRowMsg).map fun m => (m.owner, m.base)).map fun x => (x.1, x.2.e) := by
    rw [Option.map_map]
    rfl
  rw [e, rowBaseW]
  cases hm : _root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0 with
  | none =>
    rw [hm] at q
    simp at q
  | some st =>
    rw [hm, Option.map_some, Option.some.injEq] at q
    show some ((⟨parGF.place, 0⟩ : Addr), st.e) = _
    rw [q]

/-- (A3) Of the opening's messages number 0 alone has that start. -/
theorem rowOwnerW_bites : ((List.range parGF.sent.size).filter fun n =>
    decide ((ownerOf maskRowRun
        (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
          P2Law.ProofPlan.declProofFull.1)
        Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
        isMaskRowMsg).map (·.base.e) = some (maskStart parGF (rideOf (firstFold K1.qFull)) n))) =
    [0] := by
  decide +kernel

/-- (A5) The maker's free entries lie inside the mask rows' entries of number 0. -/
theorem rowFreeW : (ownerOf maskRowRun
    (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
      P2Law.ProofPlan.declProofFull.1)
    Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
    isMaskRowMsg).map (·.free) = some 8191 ∧
    (shapeAt parGF 0).maskRows * (parGF.codes.mask.getD (shapeAt parGF 0).maskCode default).ell =
      8192 := by
  decide +kernel

/-- The next message's coins of the extension field begin at 8411. -/
theorem rowNextW : (startR parGF (rideOf (firstFold K1.qFull)) 1).e = 8411 ∧
    (stepsOf parGF.codes (shapeAt parGF 0) (rideOf (firstFold K1.qFull) 0)).mask = 8192 ∧
    (stepsOf parGF.codes (shapeAt parGF 0) (rideOf (firstFold K1.qFull) 0)).maskTails = 219 := by
  decide +kernel

/-- The evaluation can fail: with number 1 for number 0 on the right the test rejects. -/
theorem rowBaseW_bent : decide ((ownerOf maskRowRun
    (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
      P2Law.ProofPlan.declProofFull.1)
    Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
    isMaskRowMsg).map (fun m => (m.owner, m.base)) =
    (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 1).map
      fun st => ((⟨parGF.place, 0⟩ : Addr), st)) = false := by
  decide +kernel

/-- THE OWNER BENT: with another part of the opening's place, or with the place of the segment's
next sending of the kind K1 (piece 4), for the owner on the right, the test rejects. -/
theorem rowBaseW_bent_owner :
    decide ((ownerOf maskRowRun
      (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
        P2Law.ProofPlan.declProofFull.1)
      Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
      isMaskRowMsg).map (fun m => (m.owner, m.base)) =
      (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0).map
        fun st => ((⟨parGF.place, 1⟩ : Addr), st)) = false ∧
    decide ((ownerOf maskRowRun
      (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
        P2Law.ProofPlan.declProofFull.1)
      Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
      isMaskRowMsg).map (fun m => (m.owner, m.base)) =
      (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0).map
        fun st => ((⟨⟨1, some 0, 4, .K1⟩, 0⟩ : Addr), st)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **THE SAME, AT THE PLAN AND THE RIDE OF THE DESCRIPTION's OWN GROUND**, under the head. -/
theorem rowOwnerW_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (ownerOf maskRowRun
        (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
          P2Law.ProofPlan.declProofFull.1)
        Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
        isMaskRowMsg).map (fun m => (m.owner, m.base.e)) =
      some ((⟨(K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place, 0⟩ : Addr),
        maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 0) := by
  rw [K1.eG_atAll h O (K1.pin1_atAll h),
    firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
  · exact rowOwnerW
  · rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tiedW
#print axioms ProofFile.Honest.K1.firstSendingW
#print axioms ProofFile.Honest.K1.rowPickW
#print axioms ProofFile.Honest.K1.rowBaseW
#print axioms ProofFile.Honest.K1.rowOwnerW
#print axioms ProofFile.Honest.K1.rowOwnerW_bites
#print axioms ProofFile.Honest.K1.rowFreeW
#print axioms ProofFile.Honest.K1.rowNextW
#print axioms ProofFile.Honest.K1.rowBaseW_bent
#print axioms ProofFile.Honest.K1.rowBaseW_bent_owner
#print axioms ProofFile.Honest.K1.rowOwnerW_head
