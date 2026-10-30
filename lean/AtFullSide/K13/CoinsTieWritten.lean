-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K13/CoinsTieWritten.lean: kind K13, the members' batching: UNDER THE LIBRARY's HEAD h:
THE KIND's TIE `CoinsTie` AT THE BORDER 355, FROM: KIND K1's RECORD OF PREMISES AT THE OPENING
(`K1Seated`) · "THE THREAD's BOOK IS THE ONE THAT THE MAKER `bookWhole` RETURNS" AT THE WRITTEN
SENDINGS · THE JOB's PLAN AND RIDE ARE THE OPENING's · three public premises. THE RECORD IS A
PREMISE: no Script is laid. THAT THE MAKER RETURNS THE THREAD's BOOK IS A PREMISE: under h it does
return a book at the three written lists of sendings (`bookWhole_returns_at_head_ahead`,
AtFullSide/K14/WholeAheadAtHead.lean); what is left is that the thread's book is that book. Two
statements with their proofs: calls; no definition; nothing is evaluated here. THE FULL SIZE AND THE
FORMAT's EARLIER HASH ALONE.

Main names: `k13_hS_of_whole_written`: **the premise hS of `k13_coinsTie_of_msgTxt`, to the letter,
from hW and two public equations on the sender's plan and ride.** `k13_coinsTie_of_seated_written`:
**the tie.**

What is gained. `k13_coinsTie_of_seated_whole`
(Johnson/Desc/ProofFile/Honest/K13/CoinsTieOfSeated.lean) has two premises on the maker's own calls,
h1 and h3. HERE BOTH ARE GONE: h3 is `k13_h3_at_head`, h1's left sides are `k13_idx_at_head`
(WantsAtHead.lean of this folder), h1's right sides are the opening's place, by the plan's own text,
and kind K1's `k1Start_head` (Honest/K1/Law/StartAtFour.lean: under h and O, at the plan and the
ride of the description's own ground, the mask entries of message number 4 begin at the sender's
value number 8647 of the extension field; `k1StartW_alone` there: of the opening's messages number 4
alone has that start). In their stead stands one public premise, hR: the job's ride is the
opening's, as hP says of its plan. NO FIELD OF THE RECORD IS AN EQUATION ON THE RIDE ALONE: two
spell it (fits: the public test at J.P and J.ride; hasCoins: the count `dueR J.P J.ride`); three
more bear the job J whole, the ride with it (half, msgs, pads: Honest/K1/Seated.lean): whether these
settle the ride at a given prover is not looked at here. WHO PAYS hR: whoever lays J: where J is a
job that `placeJob` makes at the fold `firstFold Bs.G₀.first`, it holds by that text (K1's
`ride_of_job`, Honest/K1/Law/StartAtFour.lean).

WHAT IS LEFT, BESIDE h: EIGHT; NONE IS SHOWN HERE. K: the record. O: the library's "opened" (under h
there is one). hP, hR: the job's plan and ride are the opening's at the description's own ground.
hW: `bookWhole` returns the thread's book, at the written sendings of the first chain (p1 and p2,
the other two chains' sendings, are free letters, tied to nothing), at the list `mergesByName` (the
maker's guess which masked sumchecks are merges). hshape, hfreeP: public, between the sending and
the verifier's list. hfree: numbers. THESE LAST THREE ARE SHOWN, under h, O and hP, in
CoinsTieFive.lean of this folder.

How. Calls: `k13_hS_of_whole` (Honest/K13/StretchAtHead.lean), `k13_coinsTie_of_seated`
(Honest/K13/CoinsTieOfSeated.lean), the two statements of WantsAtHead.lean of this folder, and
`k1Start_head`.

Limits. NOT IN FRONT OF A LAW OVER COINS: the ground: the Limits of Honest/K13/CoinsTieOfFacts.lean.
CONDITIONAL ON h AND THE PREMISES NAMED: that they hold together is not shown: hW AND THE RECORD's
FIELD hasCoins SPEAK OF ONE BOOK, AND DO NOT CLASH: under h, O, hP and hR the field follows from hW
by three statements of kind K1's, which no one statement joins at a book that is a letter:
`book_pick` and `rows_alike_head` (Honest/K1/Law/HasCoinsAtBook.lean: where the maker returns, the
book's first table begins with the rows that `rowsIn` yields; under h these are the written
description's) and `hasCoins_head_of` (Honest/K1/Law/HasCoinsOfRows.lean); none is imported here,
and the field stays asked inside K. hW fixes the book as the maker's value: it brings no guard and
no budget; the book is made without a look at the prover's parts. `oneStretch` reads the extension
field's entries alone. THE BASE OF THE INDEX MASKS' ENTRIES IS COUNTED BY THREE TEXTS (the sender's
`K1.maskStart` · the maker's `maskStart`, Honest/BookRows.lean · `offsetOf`,
Honest/K14/Sendings.lean): HERE THE FIRST TWO MEET IN ONE NUMBER, 8647, AT THE WRITTEN DATA, each by
its own evaluation in Lean's kernel (`k1StartW`; `rawIdx_written`): no law joins the texts. The
limits of WantsAtHead.lean of this folder and of Honest/K13/CoinsTieOfSeated.lean and
Honest/K13/StretchAtHead.lean bind here too. WHERE `lendRow` ERRS AT THE KIND's ROW THE TIE HOLDS
FOR NOTHING: at the book that `bookWhole` returns at the head's own three lists of sendings it
returns, under h (`k13_lendRow_at_head`, LendRowAtHead.lean of this folder; not imported here); at
other p1, p2 nothing is said. `k13_coinsTie_of_seated_written` is called by CoinsTieFive.lean of
this folder alone; the other by nothing outside this file.

What is not claimed. That any premise holds. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import AtFullSide.K13.WantsAtHead
import Johnson.Desc.ProofFile.Honest.K13.CoinsTieOfSeated
import Johnson.Desc.ProofFile.Honest.K1.Law.StartAtFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound (MsgT Mem)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.W (indexFree0)
open ProofFile.Honest.K1 (K1Seated PlaceIn)
open AtFullSide.K14 (rawIdxW)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **hS FROM "THE BOOK IS THE MAKER's" AND TWO PUBLIC EQUATIONS ON THE SENDER's PLAN AND RIDE.** IT
SHOWS hS AT NO BOOK, AND PAYS NOTHING OF THAT DEBT BY ITSELF: hW (`bookWhole` RETURNS THE THREAD's
BOOK, at the written sendings) IS A PREMISE: that the book which it returns is the thread's is shown
nowhere. `k13_hS_of_whole` with h3 paid by `k13_h3_at_head` and h1's left sides by
`k13_idx_at_head`. CONDITIONAL on h. -/
theorem k13_hS_of_whole_written {p1 p2 : Johnson.G.ChainSends} {W' Y' : Type}
    (J : K1.SendJob W' Y') (n : ℕ)
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 p1 p2
      (mergesByName cF.blocksInOrder) = .ok Bk)
    (hplace : J.P.place = ⟨1, some 0, 1, .K1⟩) (hstart : K1.maskStart J.P J.ride n = 8647) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[355]? =
        some blk →
      oneStretch (rowEntries Bk blk.place 2 0) =
        some (⟨J.P.place, 0⟩, K1.maskStart J.P J.ride n + 13, 2 * h.𝔇.P13.lin.kCol + 1) :=
  k13_hS_of_whole h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ J n hW
    (fun idx hi => by
      obtain rfl : rawIdxW = idx := Option.some.inj ((k13_idx_at_head h).symm.trans hi)
      exact ⟨by rw [hplace]; rfl, by rw [hstart]; rfl⟩)
    (k13_h3_at_head h)

/-- THE RECORD IS A PREMISE: no Script is laid. hW (`bookWhole` RETURNS THE THREAD's BOOK, at the
written sendings) IS A PREMISE: THAT THE BOOK WHICH IT RETURNS IS THE THREAD's IS SHOWN NOWHERE.
**`CoinsTie` AT THE HEAD, AT THE BORDER 355, FROM KIND K1's RECORD AT THE OPENING, "THE BOOK IS THE
MAKER's", AND THAT THE JOB's PLAN AND RIDE ARE THE OPENING's** (hP, hR): `k13_coinsTie_of_seated`
with its premise hS handed over by `k13_hS_of_whole_written` at n = 4. CONDITIONAL on h and eight
premises. -/
theorem k13_coinsTie_of_seated_written {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {Bs : ProofFile.PureBase} {base₀ : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {blk₂ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : K1.SendJob (PlaceIn ProofFile.Inst) X'} {own₀ : X'} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
    {rad : ℕ → ℕ}
    (K : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 2 blk₂ wit J
      own₀ .opening (P5J.At.arr Zp) seats₀ ms rad)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (hshape : (msgsOfChain Zp.made.proof.1)[4]? = some (shapeAt J.P 4))
    (hfreeP : indexFree0 Zp cF ≤ Send.freeMaskEntries (shapeAt J.P 4).maskRows
      (J.P.codes.mask.getD (shapeAt J.P 4).maskCode default).ell (shapeAt J.P 4).answers)
    {p1 p2 : Johnson.G.ChainSends}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 p1 p2
      (mergesByName cF.blocksInOrder) = .ok Bk)
    (hfree : 13 + (2 * h.𝔇.P13.lin.kCol + 1) ≤ indexFree0 Zp cF) :
    CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 355 weights pile h.𝔇.P13
      (k13ReaderAt h) :=
  k13_coinsTie_of_seated h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ O K hP hshape hfreeP
    (k13_hS_of_whole_written h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ J 4 hW
      (by rw [hP]; rfl) (by rw [hP, hR]; exact K1.k1Start_head h O)) hfree

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_hS_of_whole_written
#print axioms AtFullSide.K13.k13_coinsTie_of_seated_written
