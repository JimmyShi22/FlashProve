-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K4/MaskRowsLaterW.lean: PUBLIC DATA ALONE: seats, numbers of
messages, places, counts, starts: where a message sits and where its entries begin among its
sender's coins, never what stands in it. Two definitions (a public test with code; a written value);
closed facts, each by an evaluation in Lean's kernel (`decide +kernel`, as the files that it follows
do); laws under the library's head h and an opening O.

What is here. THE MESSAGE THAT HOLDS THE MASK ROW WHICH THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4) READ AT THE GROUPS g = 1, …, 11 IS MESSAGE NUMBER 2 OF THE CODE SWITCH (the kind
K2) AT THE PLACE WHOSE FIELD link IS 2 g. In the sending "link 2 g, moment 0" stand, in this order:
the carried message, one kept copy, the segment's own messages of moment 0, the fold's fresh mask;
number 2 is the first of the segment's own. IT IS NOT THE SWITCH's LAST MESSAGE.
  `rowAtB` p n base   THE TEST, at a place p: n is not the last message and lies below the number of
      p's messages; the switch is its first sender; it has one mask row; its mask row has 8192
      entries; these begin at number base among the sending's coins of the extension field
      (`maskBase`, Honest/K2/Law/MaskCoin.lean, of K2's authors); p's place is `switchPlaceAt`
      p.link
  `rowLaterW` g   the written value: the maker's row at the link 2 g
At the written lists:
  `maskHitLaterW`   the search inside `k4MaskMsg` (Honest/K4/Lot/MaskNum.lean) HITS at each segment
      2 g, at index 0: the 0 is no default. CALLED BY NO LAW: it stands beside `numPickW`, which
      would read the same at a search that missed
  `numPickW`   at each of the eleven links the written list of places has a place, and of ITS
      messages number 2 ALONE bears K4's number `maskNumW` (2 g)
      (Honest/K4/Law/W/MaskNumsApart.lean). IT IS ITS OWN NEGATIVE TEST: the other numbers, the last
      among them, are shut out
  `rowAtW`   at each of the eleven that place passes `rowAtB` at n := 2, base := 439
  `rowAtW_can_fail`   CONTROLS: at the link 2 the test says no at base := 440, at n := 1 (a kept
      copy) and at n := 5 (the last); at the link 3, where a place stands too, it says no at n := 2.
      WHICH CLAUSES FAIL AT EACH LEAN DOES NOT SAY; reckoned by hand, once: at 440 the
      clause on the start alone; at each of the other three more than one
  `rowAtW_place_bites`   A CONTROL THAT BITES THE SIXTH CLAUSE ALONE: at the link 24, at n := 2 and
      base := 439, the five other clauses hold and the test says no: that place is not
      `switchPlaceAt` 24
  `rowsLaterW`   each (2 g, `rowLaterW` g) is a member of the library's 25 written rows `rawRowsW`
      (AtFullSide/K14/RawFactsWritten.lean)
Under h (and, where it is named, O):
  `maskNum_later` (h)   **`switchNum` Zp p 2 = `k4MaskNum` Zp (2 * g)** at every p with p.link =
      2 g: the like, for the eleven, of K1's authors' `maskNum_zero`
      (AtFullSide/K1/OpeningSeatsK4.lean)
  `rowLater_at_head` (h)   the maker `ownerOf` at the head's own lists, at the label "link 2 g,
      moment 0", yields `rowLaterW` g: our `rowOwner_at_head` (AtFullSide/K4/OwnersAtHead.lean)
  `later_seam` (h, O)   **THE SEAM TO THE MAKER's ROW**: the plan's own list of the kind's places
      has a place p with p.link = 2 g at which: the number is K4's; the row's owner is ⟨p.place, 0⟩;
      the row's start base.e is `maskBase` … 2; and the four clauses of the test that a caller of
      K2's authors' `msgTxt_mask` and `share_msgs_fit` needs

WHICH STEP IS HAD BY WHICH CALL. The written lists in the head's stead: `switchNum_at_head`,
`places_at_head` (Honest/K2/Law/SwitchNumsAtHead.lean, PlacesWritten.lean, of K2's authors),
`maskNumAt_written` (ours), `written_of_head` (Johnson/Road/K4/K4HeadWritten.lean).

Not shown here. EMPTINESS FIRST: the closed facts have no premise. The laws are conditional on h
(and O): that h holds anywhere is not said here; the side library has a member of h at one place
(AtFullSide/Top/HeadMemberAtFull.lean, with its own Limits); an opening is drawn out of h
(h.laid.opened). g = 0 is shut out by h1: there the sender is K1's opening. THAT THE SWITCH AT p IS
THE ONLY SENDER OF A LOT WITH THAT NUMBER IN ANY LIST OF LOTS is not said. That the written lists
are the planner's at the public files rests on the files named. WHO ELSE IS GIVEN THE COINS FROM
THAT START ON, and under which mark, is not said here. That the start of the switch's LAST message
lies behind the row: AtFullSide/K4/MaskRowsLaterBeyondW.lean. The full size and the format's
second hash function alone. Nothing on a run, or on what any coin is. Nothing on soundness, on completeness
or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskNumsApart
import AtFullSide.K4.OwnersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K4
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace switchSent switchFresh firstSender switchNum switchNumIn
  switchPlaces maskBase maskLength)
open ProofFile.Honest.K2.Law (placesW places_at_head switchNum_at_head)
open ProofFile.Honest.K4.Lot (k4MaskNum)
open ProofFile.Honest.K4.W (maskNumW maskNumAt_written)
open AtFullSide.K14 (rawRowsW)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (messagesAt)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt)
open OnBytes.Road.K4 (sentW written_of_head)
open OnBytes.Maker (WholeD)
open P5T (seatsAllFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST** at a place of the code switch, a message's number n and a start base. -/
def rowAtB (p : SwitchPlace) (n base : ℕ) : Bool :=
  decide (n + 1 < (switchSent p.sizes p.others).size ∧ firstSender p n = true ∧
    ((switchSent p.sizes p.others).getD n default).shape.maskRows = 1 ∧
    maskLength p.sizes.codes (switchSent p.sizes p.others) n = 8192 ∧
    maskBase p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n = base ∧
    p.place = switchPlaceAt p.link)

/-- The maker's row at the link 2 g, written: g is meant from 1 to 11. -/
def rowLaterW (g : ℕ) : MsgAt := ⟨maskRowRun, ⟨switchPlaceAt (2 * g), 0⟩, ⟨23436, 439⟩, 8191⟩

/-! ## 1 At the written lists -/

set_option maxRecDepth 1000000 in
/-- At each segment 2 g, g from 1 to 11, of the written request the search for a message with mask
rows hits, at index 0. -/
theorem maskHitLaterW : ((List.range 11).all fun i =>
    decide (((messagesAt sentW (2 * (i + 1))).findIdx? fun y => y.shape.maskRows != 0) =
      some 0)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Of the messages of the written place with the link 2 g, number 2 alone bears K4's number.** -/
theorem numPickW : ((List.range 11).all fun i =>
    (placesW.find? fun p => p.link == 2 * (i + 1)).any fun p =>
      decide (((List.range (switchSent p.sizes p.others).size).filter fun n =>
        switchNumIn seatsAllFull p.link n == maskNumW (2 * (i + 1))) = [2])) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **That place passes the test at n := 2 and base := 439.** -/
theorem rowAtW : ((List.range 11).all fun i =>
    (placesW.find? fun p => p.link == 2 * (i + 1)).any fun p => rowAtB p 2 439) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- CONTROLS: the test can say no. -/
theorem rowAtW_can_fail :
    ((placesW.find? fun p => p.link == 2).any fun p => rowAtB p 2 440) = false ∧
      ((placesW.find? fun p => p.link == 2).any fun p => rowAtB p 1 439) = false ∧
      ((placesW.find? fun p => p.link == 2).any fun p => rowAtB p 5 439) = false ∧
      ((placesW.find? fun p => p.link == 3).any fun p => rowAtB p 2 439) = false ∧
      (placesW.find? fun p => p.link == 3).isSome = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A CONTROL ON THE CLAUSE «p.place = switchPlaceAt p.link» ALONE: at the written place with the
link 24 the test says no, and its five other clauses hold there. -/
theorem rowAtW_place_bites :
    ((placesW.find? fun p => p.link == 24).any fun p => rowAtB p 2 439) = false ∧
      ((placesW.find? fun p => p.link == 24).any fun p =>
        decide (2 + 1 < (switchSent p.sizes p.others).size ∧ firstSender p 2 = true ∧
          ((switchSent p.sizes p.others).getD 2 default).shape.maskRows = 1 ∧
          maskLength p.sizes.codes (switchSent p.sizes p.others) 2 = 8192 ∧
          maskBase p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) 2 = 439)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each written value is the library's written row of its link. -/
theorem rowsLaterW : ((List.range 11).all fun i =>
    decide ((2 * (i + 1), rowLaterW (i + 1)) ∈ rawRowsW)) = true := by
  decide +kernel

/-! ## 2 What the test gives -/

/-- A group from 1 to 11 is the successor of a number below 11. -/
theorem later_pred {g : ℕ} (h1 : 1 ≤ g) (hg : g < 12) : ∃ i, i < 11 ∧ g = i + 1 :=
  ⟨g - 1, by omega, by omega⟩

/-- The test's yes, as a sentence. -/
theorem rowAtB_gives {p : SwitchPlace} {n base : ℕ} (h : rowAtB p n base = true) :
    n + 1 < (switchSent p.sizes p.others).size ∧ firstSender p n = true ∧
      ((switchSent p.sizes p.others).getD n default).shape.maskRows = 1 ∧
      maskLength p.sizes.codes (switchSent p.sizes p.others) n = 8192 ∧
      maskBase p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) n = base ∧
      p.place = switchPlaceAt p.link :=
  of_decide_eq_true h

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- h, h1, hg AND hl ARE PREMISES. **THE NUMBER OF THE SWITCH's MESSAGE NUMBER 2 IS K4's NUMBER OF
SEGMENT 2 g's MASK ROW's MESSAGE**, in the form in which K4's laws take it of the sender's lot. -/
theorem maskNum_later (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (h1 : 1 ≤ g)
    (hg : g < 12) {p : SwitchPlace} (hl : p.link = 2 * g) :
    switchNum Zp p 2 = k4MaskNum Zp (2 * g) := by
  obtain ⟨i, hi, rfl⟩ := later_pred h1 hg
  have t : ((placesW.find? fun p => p.link == 2 * (i + 1)).any fun p =>
      decide (((List.range (switchSent p.sizes p.others).size).filter fun n =>
        switchNumIn seatsAllFull p.link n == maskNumW (2 * (i + 1))) = [2])) = true :=
    List.all_eq_true.1 numPickW i (List.mem_range.2 hi)
  cases hf : (placesW.find? fun p => p.link == 2 * (i + 1)) with
  | none =>
    rw [hf] at t
    cases t
  | some q =>
    rw [hf, Option.any_some] at t
    have hq0 := List.find?_some hf
    have hq : q.link = 2 * (i + 1) := beq_iff_eq.1 hq0
    have hm : 2 ∈ (List.range (switchSent q.sizes q.others).size).filter fun n =>
        switchNumIn seatsAllFull q.link n == maskNumW (2 * (i + 1)) := by
      rw [of_decide_eq_true t]
      exact List.mem_singleton.2 rfl
    have e : switchNumIn seatsAllFull q.link 2 = maskNumW (2 * (i + 1)) :=
      beq_iff_eq.1 (List.mem_filter.1 hm).2
    rw [hq] at e
    rw [switchNum_at_head h.toAtMg]
    show switchNumIn seatsAllFull p.link 2 = k4MaskNum Zp (2 * (i + 1))
    rw [hl, e]
    exact (maskNumAt_written (written_of_head h.toAtMg) (2 * (i + 1))).symm

/-- h, h1 AND hg ARE PREMISES. **The maker's row at the link 2 g, at the head's own lists, is the
written value.** -/
theorem rowLater_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (h1 : 1 ≤ g)
    (hg : g < 12) :
    ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
        ((F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        s!"link {2 * g}, moment 0" isMaskRowMsg = some (rowLaterW g) := by
  obtain ⟨i, hi, rfl⟩ := later_pred h1 hg
  exact rowOwner_at_head h (2 * (i + 1), rowLaterW (i + 1))
    (of_decide_eq_true (List.all_eq_true.1 rowsLaterW i (List.mem_range.2 hi)))

/-- h, O, h1 AND hg ARE PREMISES. **THE SEAM TO THE MAKER's ROW, AT EACH OF THE ELEVEN LATER
GROUPS.** -/
theorem later_seam (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (h1 : 1 ≤ g) (hg : g < 12) :
    ∃ p ∈ switchPlaces Zp Bs.G₀, p.link = 2 * g ∧ switchNum Zp p 2 = k4MaskNum Zp (2 * g) ∧
      (rowLaterW g).owner = ⟨p.place, 0⟩ ∧
      (rowLaterW g).base.e = maskBase p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) 2 ∧
      2 + 1 < (switchSent p.sizes p.others).size ∧ firstSender p 2 = true ∧
      ((switchSent p.sizes p.others).getD 2 default).shape.maskRows = 1 ∧
      maskLength p.sizes.codes (switchSent p.sizes p.others) 2 = 8192 := by
  obtain ⟨i, hi, hgi⟩ := later_pred h1 hg
  have t : ((placesW.find? fun p => p.link == 2 * (i + 1)).any fun p => rowAtB p 2 439) = true :=
    List.all_eq_true.1 rowAtW i (List.mem_range.2 hi)
  rw [places_at_head h.toAtMg O]
  cases hf : (placesW.find? fun p => p.link == 2 * (i + 1)) with
  | none =>
    rw [hf] at t
    cases t
  | some p =>
    rw [hf, Option.any_some] at t
    have hl0 := List.find?_some hf
    have hl : p.link = 2 * g := by
      rw [hgi]
      exact beq_iff_eq.1 hl0
    obtain ⟨a, b, c, d, e, f⟩ := rowAtB_gives t
    refine ⟨p, List.mem_of_find?_eq_some hf, hl, maskNum_later h h1 hg hl, ?_, e.symm, a, b, c, d⟩
    show (⟨switchPlaceAt (2 * g), 0⟩ : Addr) = ⟨p.place, 0⟩
    rw [f, hl]

end AtFullSide.K4

#print axioms AtFullSide.K4.rowAtB
#print axioms AtFullSide.K4.rowLaterW
#print axioms AtFullSide.K4.maskHitLaterW
#print axioms AtFullSide.K4.numPickW
#print axioms AtFullSide.K4.rowAtW
#print axioms AtFullSide.K4.rowAtW_can_fail
#print axioms AtFullSide.K4.rowAtW_place_bites
#print axioms AtFullSide.K4.rowsLaterW
#print axioms AtFullSide.K4.later_pred
#print axioms AtFullSide.K4.rowAtB_gives
#print axioms AtFullSide.K4.maskNum_later
#print axioms AtFullSide.K4.rowLater_at_head
#print axioms AtFullSide.K4.later_seam
