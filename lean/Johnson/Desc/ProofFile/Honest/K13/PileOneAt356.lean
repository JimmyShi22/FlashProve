-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileOneAt356.lean: kind K13, the members' batching: UNDER THE
LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE, h (`P5J.AtMgA`): THE SHARE OF THE EXCHANGE AT THE ITEM
"pileOne", AT NUMBER 356 OF THE FIRST CHAIN's THREAD (the place "M:4", the sending of W): behind
that sub-protocol's accepted step the item holds, if the thread stands in front. No premise beside
h. Statements with their proofs; no definition. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `k13_len356`: under h the first chain has at least 356 sub-protocols (numbers 0 to 355:
what the BORDER 356 wants; that number 356 itself is there is neither shown nor needed here).
`k13_public_at_356`: **wherever the thread stands at the border 356, the seven sentences of
`PublicAtM4` (ExchangeM4.lean of this folder) hold of the verifier's state.** `k13_pileOne_at_356`:
**the share, from the thread** (`ExchangeAt`, Honest/Thread/Shares.lean). `k13_pileOneS_at_356`:
from the pair "the thread and what is said", at every Said (`ExchangeAtS`,
Honest/Thread/SharesS.lean).

Why. The item "pileOne" is the kind's: it is open in front of number 356 and that row owes it again.
`pileOne_at_letters` (ExchangeM4At.lean of this folder) has the share from one premise: `PublicAtM4`
from the thread in front. Here that premise is shown at the frame's own laying of the thread
(`lettersHead`, Honest/Thread/FirstHead.lean). `k13_public_at_356` pays the same premise of
`exchange_at_letters` and `exchange_whole_at_letters` (ExchangeM4At.lean) and the field pub of
`K13SeatedM4` (SeatedM4.lean) at these letters: no call is typed. Of the seven sentences the share
at "pileOne" spends four (masks, there, book, tree); claim, room and within are spent at the item
wrow alone.

How, sentence by sentence. claim: `claim_at_m4` (ClaimAtM4.lean of this folder). room: one step back
over the kind's own sub-protocol (`thr_back_decide`, Honest/Thread/ReachBack.lean; `MemberIs.back`)
and the library's `atM3_fits` (Johnson/Desc/K13/Law/M3Fits.lean). masks, within: the library's
`FoldFacts` wherever the thread stands (`foldFacts_thr`, Honest/Thread/ReachFacts.lean): its fields
pileMasks and pileWithin. there: the promise's public test "indexThere", which the table lays
wherever the item pinI is open (`indexThere_at`, `pin_at`, Johnson/HB/LLHARD/IndexOpenWritten.lean),
drawn out of the thread's form by `xk_of_form` (Honest/Thread/FormXK.lean) and the library's
`IM.xk_parts` (Johnson/IMR/HandsDef.lean), as `indexFacts_thr` itself does. book: `indexFacts_thr`
(Honest/K4/Law/W/IndexFactsThr.lean) at the border 356. tree: the library's `place_in_book`
(Johnson/Desc/K12/Door/DoorGives.lean).

Limits. CONDITIONAL ON h: that h can be met is not shown here (Honest/Thread/FirstHead.lean's head
says what is had of it). THE SHARE IS A PREMISE's FORM: it says "IF the thread stands in front of
number 356 and the sub-protocol's step is accepted, THEN the item holds behind": not that the thread
stands at any run: AT LETTERS AT WHICH IT STANDS NOWHERE ALL THREE HOLD IDLY. THE TWO SHARES ALSO
BEGIN "if number 356 is there" (`ExchangeAt`, Honest/Thread/Shares.lean): that it is there is not
shown here. ALL FOUR STATEMENTS REST ON CLOSED FACTS THAT LEAN's KERNEL HAS EVALUATED BENEATH
(`m3_place`, FromThreadAt.lean of this folder; `pinOpen_written`, `open_count`,
Johnson/HB/LLHARD/IndexOpenWritten.lean), which no independent checker has replayed. Nothing is
asked of the prover's halves, the Script, the book of coins or what W's sending lays. `k13_len356`
is called by AtFullSide/K13/GAt356.lean and WitnessHasWAt356.lean and by
AtFullSide/K12/WSaysRest.lean and LettersReadyW.lean; `k13_public_at_356` by WRowAt356.lean of this
folder and by AtFullSide/K13/WitnessHasWAt356.lean; `k13_pileOneS_at_356` by
AtFullSide/K1/FiveAtBorderW.lean, AtFullSide/K13/WitnessHasWAt356.lean and
Johnson/AtFull/Shape/Scope/OwesK1.lean; `k13_pileOne_at_356` by no other file. This file's imports
reach Johnson/Goal/, by the hypothesis h (`P5J.AtMgA`).

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4At
import Johnson.Desc.ProofFile.Honest.K13.ClaimAtM4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexFactsThr
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.Desc.First.EPubAt
import Johnson.Road.K4.More.FrontList
import Johnson.IMR.HandsDef
import Johnson.Desc.K13.Law.M3Fits
import Johnson.Desc.K12.Door.DoorGives
import Johnson.HB.LLHARD.IndexOpenWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item Pub ePubAt ePubAt_mem pubHeld pubSets openSets start)
open VerifiableInference.Desc.K12.Door (place_in_book)
open VerifiableInference.Desc.K13 (whereOf indexThereC)
open VerifiableInference.Desc.K13.Law (pin_at indexThere_at atM3_fits)
open VerifiableInference.Desc.Sound (MsgT mgAll_more_base linksFull moreAll)
open OnBytes.Road.K4.More (PS)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead foldFacts_thr xk_of_form)
open ProofFile.Honest.K4.W (indexFacts_thr)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- Under h the first chain has at least 356 sub-protocols: numbers 0 to 355: what the border 356
wants. -/
theorem k13_len356 : 356 ≤ cF.blocksInOrder.length := by
  cases hb : cF.blocksInOrder[355]? with
  | none =>
    have e : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[355]? = none := by
      show (cF.blocksInOrder.map (·.place))[355]? = none
      rw [List.getElem?_map, hb]
      rfl
    rw [P5J.At.places_paid h.scope h.reads h.laid, m3_place] at e
    cases e
  | some blk => exact (List.getElem?_eq_some_iff.1 hb).1

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SEVEN SENTENCES ON THE VERIFIER's PUBLIC STATE, WHEREVER THE THREAD STANDS AT 356.**
CONDITIONAL on h. -/
theorem k13_public_at_356 {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356 k s m En) :
    PublicAtM4 (whereOf Zp) s := by
  have hlen := k13_len356 h
  have hpin := pin_at (k := 356) (by decide) (by decide)
  obtain ⟨sh, F⟩ := indexFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hlen (by decide)
    hpin hT
  have hm : s.failed = none := by
    have hT' := hT
    unfold Thr at hT'
    obtain ⟨-, -, hF, -⟩ := hT'
    have e : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.mp e
  have FF := foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
  have fm := FF.pileMasks 356 (m.st.input.x.pub, s) ⟨hlen, k, m, En, hT, rfl⟩ hm
  have fw := FF.pileWithin 356 (m.st.input.x.pub, s) ⟨hlen, k, m, En, hT, rfl⟩ hm
  have fw' : VerifiableInference.Desc.K13.rowsWithinC s = true := by
    have e : (VerifiableInference.Desc.K13.ledgersFitC s &&
      VerifiableInference.Desc.K13.rowsWithinC s) = true := fw
    rw [Bool.and_eq_true] at e
    exact e.2
  have hX := IM.xk_parts (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁)
    (by
      have hT' := hT
      unfold Thr at hT'
      exact hT'.2.2.1))
  have t2 : pubHeld (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP
      ((openSets linksFull PS (start linksFull))[356]?.getD [])
      ((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.more linksFull
        PS)[356]?.getD []) (m.st.input.x.pub, s) = true := by
    have e := hX.2.2.2.2
    unfold P1K2.EQ at e
    rw [Bool.and_eq_true] at e
    exact e.2
  have hE : ePubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.pub moreAll
      linksFull PS 356 (m.st.input.x.pub, s) = true := by
    have eM : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.more = moreAll :=
      mgAll_more_base h.𝔇
    have hE0 : ePubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.pub
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.more linksFull PS 356
        (m.st.input.x.pub, s) = true := t2
    rw [eM] at hE0
    exact hE0
  have q : indexThereC s = true := ePubAt_mem _ _ _ _ _ _ hE Pub.indexThere
    (Or.inr (indexThere_at (k := 356) (by decide) (by decide)))
  have hthere : s.out.indexMasks < s.st.oracles.size := by
    unfold indexThereC at q
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at q
    cases q
  obtain ⟨s₀, blk, rs, gs, hblk, _, hd⟩ := thr_back_decide
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).first
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf m.st.input.x) (b := 355)
    hlen (fun _ h0 => h0) hT
  exact {
    claim := claim_at_m4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁)
      (k13_memberIs_at h) hlen hT
    room := atM3_fits ((k13_memberIs_at h).back blk hblk s₀ rs gs s hd)
    masks := fm
    within := fw'
    there := hthere
    book := F.hs
    tree := fun q' hq' => by
      obtain ⟨q'', e, hlt⟩ := place_in_book F.h₃ F.hs F.hb s.out.indexMasks hthere
      rw [hq'] at e
      cases e
      exact hlt }

/-- **THE SHARE OF THE EXCHANGE AT "pileOne", AT NUMBER 356: FROM THE THREAD.** CONDITIONAL on h. -/
theorem k13_pileOne_at_356 :
    ExchangeAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356 Item.pileOne :=
  pileOne_at_letters h H.first Q _ _ test carryX item n₁ n₂ _ _ _ fun _ _ _ _ hT =>
    k13_public_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT

/-- **FROM THE PAIR, AT EVERY Said.** CONDITIONAL on h. -/
theorem k13_pileOneS_at_356
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
      Item.pileOne :=
  exchangeAtS_of _ Said (k13_pileOne_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_len356
#print axioms ProofFile.Honest.K13.k13_public_at_356
#print axioms ProofFile.Honest.K13.k13_pileOne_at_356
#print axioms ProofFile.Honest.K13.k13_pileOneS_at_356
