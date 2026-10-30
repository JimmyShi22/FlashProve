-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLOwedAtHead.lean

It states no goal. No property of the protocol is claimed.

The public test `switchLotReady`
(LotLOwedLetters.lean) AT THE REAL CLOSING PLACE: the finish of the code switch (`finishAt`,
K12/AtProof/JobL.lean) under the library's head, at the maker's book, at the first chain's number 0:
all its clauses but the closing's own, which stays a premise. So there the three that the tie of the
words asks beside itself are had: NoWord and the sizes; something is handed; the lot's rows return.

  `sampled_written`, `sampled_written_can_fail`   a closed line: at each written place every message
                        with a main row is sampled; the control: with the answers struck, no
  `finish_two_messages`  a closed line: the written finish announces just two messages
  `finish_is_written`    under the head the finish is the written one, and a member of the written list
  `book_is_written`      the maker's book at the head's description is its book at the written one
  `lookDue_first`        at the first chain the counts that may be handed are the table's
  `switchLotReady_at_head`   THE TEST SAYS YES, from hok
  `switch_lot_returns_at_closing_place`   THE THREE, at every run's coins, every input whose public
                        instance passes `publicOk`, every list of challenges
  `closing_place_and_book_are_there`   the premises hB, hG, hf can be met together under the head

By what. `switch_lends_at_written` (AtFullSide/K14/SwitchesLend.lean): `lendsPart` accepts at each
written place at the book of the written description · `bookWhole_returns_written`
(AtFullSide/K14/BookWholeWritten.lean), `bookWhole_same_at_laid` (Honest/K14/BookWholeAtHead.lean) ·
`places_head`, `finishW`, `fitsL_head_L` (AtFullSide/K12/FitsAtHeadL.lean) · `servesW`, `roomyW`,
`fitsW` (Honest/K2/Law/PublicAtWritten.lean) · `look_dueIs` (Honest/Small/LendsRow.lean),
`K1.look_due` (Honest/K1/ScriptAtLaw.lean) · `switch_lot_returns` (LotLOwedLetters.lean).

Hypotheses. h: the head. hB: Bk is the maker's book at the head's description. hG: G is the blank
ground. hf: pl is the finish. hok: the closing's public test at pl and the segments in front of it.
In the last clause: the filling's public test at the input's public instance.

Limits.
- hok IS A PREMISE: shown at no segments here. The segments and the layout are letters.
- WITH EVERY CITATION OF SwitchesLend.lean GOES ITS SENTENCE: `lendsPart` asks name, count and that
  the owners' cuts fit: it holds as well at a book that lends another owner's coins of that count.
  «Handed something» is not «handed its own coins, once».
- On whether something is handed and whether the rows return: nothing on what they are.
- The full size alone. Closed lines by Lean's kernel.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedLetters
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtWritten
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead
import AtFullSide.K14.SwitchesLend
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K2.Law (SwitchCoins placesW)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)
open P5J (TS)

/-! ## 1 Closed lines at the written places -/

set_option maxRecDepth 1000000 in
/-- **At each written place every message with a main row is sampled.** -/
theorem sampled_written :
    (placesW.all fun p => K2.noWord (K2.switchSent p.sizes p.others)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: with every message's number of answers struck to 0, no written place passes. -/
theorem sampled_written_can_fail :
    (placesW.any fun p => K2.noWord ((K2.switchSent p.sizes p.others).map fun x =>
      { x with shape := { x.shape with answers := 0 } })) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The written finish announces just two messages.** -/
theorem finish_two_messages :
    finishW.map (fun p => (K2.switchSent p.sizes p.others).size) = some 2 := by decide +kernel

/-! ## 2 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- Under the head the finish is the written one, and a member of the written list. -/
theorem finish_is_written (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) : finishW = some pl ∧ pl ∈ placesW := by
  have e : finishAt Zp G = finishW := by
    unfold finishAt finishW
    rw [places_head h hG]
  have hw : finishW = some pl := e.symm.trans hf
  exact ⟨hw, List.mem_of_find?_eq_some hw⟩

/-- The maker's book at the head's description is its book at the written description. -/
theorem book_is_written (h : P5J.AtMg o Z D₀ r₀ Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk := by
  obtain ⟨B₀, h₀⟩ := AtFullSide.K14.bookWhole_returns_written
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ h.scope h.laid).symm.trans hB)
  exact h₀

/-- At the first chain the counts that may be handed are the table's. -/
theorem lookDue_first (B : ProverCoinCounts) : lookDue B 0 = dueAt (B.rowsOf 0) :=
  funext fun a => (look_dueIs (default : Coins B) 0 a).symm.trans
    (ProofFile.Honest.K1.look_due (default : Coins B) 0 (Nat.zero_le 1) a)

/-- **THE PUBLIC TEST SAYS YES AT THE REAL CLOSING PLACE AND THE MAKER's BOOK**, from the closing's own
test. -/
theorem switchLotReady_at_head (h : P5J.AtMg o Z D₀ r₀ Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (segs : List K2.SegmentPub)
    (hok : K2.closingOk K2.freshTable (segs.take pl.link) pl = true) :
    switchLotReady Bk 0 segs pl = true := by
  obtain ⟨hw, hm⟩ := finish_is_written h hG hf
  have hl := AtFullSide.K14.switch_lends_at_written (book_is_written h hB) hm
  rw [lookDue_first] at hl
  have h2 := finish_two_messages
  rw [hw] at h2
  have h2' : (K2.switchSent pl.sizes pl.others).size = 2 := Option.some.inj h2
  unfold switchLotReady
  rw [hl, hok, List.all_eq_true.1 K2.Law.servesW pl hm, List.all_eq_true.1 K2.Law.roomyW pl hm,
    List.all_eq_true.1 K2.Law.fitsW pl hm, List.all_eq_true.1 sampled_written pl hm, h2']
  rfl

/-- **THE THREE AT THE REAL CLOSING PLACE.** No message with a main row goes unsampled; the sending has
messages 0 and 1; at every run's coins the frame hands the switch's part coins at the first chain's
number, and at them the lot's rows return, at every input whose public instance passes the filling's
test and at every list of challenges. -/
theorem switch_lot_returns_at_closing_place (h : P5J.AtMg o Z D₀ r₀ Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub)
    (hok : K2.closingOk K2.freshTable (segs.take pl.link) pl = true) :
    K2.NoWord (K2.switchSent pl.sizes pl.others) ∧ 0 < (K2.switchSent pl.sizes pl.others).size ∧
      1 < (K2.switchSent pl.sizes pl.others).size ∧
      ∀ (k : Coins Bk) (w : Local W₀ Rc Xi Tr),
        K2.publicOk D lay pl (segs.take pl.link) w.x = true → ∀ hd : List Fmt.Drawn,
          ∃ (c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries)
            (V : ℕ → Johnson.Prover.Send.Rows), K2.handed 0 pl k = some c ∧
              K2.switchRowsLaid D readers (K2.lotClosingAt lay segs) pl c w hd = .ok V :=
  switch_lot_returns 0 (Nat.zero_le 1) D readers lay segs pl
    (switchLotReady_at_head h hB hG hf segs hok)

/-- **The premises hB, hG and hf can be met together**: under the head there are the maker's book, the
blank ground and the finish. -/
theorem closing_place_and_book_are_there (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) :
    ∃ (Bk : ProverCoinCounts) (G : ProofFile.Ground) (pl : K2.SwitchPlace),
      bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
        (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk ∧
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧ finishAt Zp G = some pl := by
  obtain ⟨B₀, h₀⟩ := AtFullSide.K14.bookWhole_returns_written
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨pl, hf, -⟩ := fitsL_head_L h O.blank
  exact ⟨B₀, Bs.G₀, pl, ProofFile.Honest.K14.bookWhole_same_at_laid h₀ h.scope h.laid, O.blank, hf⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.sampled_written
#print axioms ProofFile.Honest.K12.AtProof.sampled_written_can_fail
#print axioms ProofFile.Honest.K12.AtProof.finish_two_messages
#print axioms ProofFile.Honest.K12.AtProof.finish_is_written
#print axioms ProofFile.Honest.K12.AtProof.book_is_written
#print axioms ProofFile.Honest.K12.AtProof.lookDue_first
#print axioms ProofFile.Honest.K12.AtProof.switchLotReady_at_head
#print axioms ProofFile.Honest.K12.AtProof.switch_lot_returns_at_closing_place
#print axioms ProofFile.Honest.K12.AtProof.closing_place_and_book_are_there
