-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CoinsTieOfSeated.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h AND KIND K1's RECORD OF PREMISES `K1Seated` (Honest/K1/Seated.lean) AT THE OPENING:
`CoinsTie` AT THE BORDER 355. THE RECORD IS A PREMISE: no Script is laid. Two statements with their
proofs; no definition. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `k13_coinsTie_of_seated`: **the tie from the record.** `k13_coinsTie_of_seated_whole`:
**the same with its premise on the book, hS, handed over by `k13_hS_of_whole`** (StretchAtHead.lean
of this folder): in hS's stead: hW (the maker `bookWhole` returns the thread's book), h1 and h3, at
n = 4.

What it does. It is `k13_coinsTie_of_msgTxt` (CoinsTieAtHead.lean of this folder) with the sender's
message number laid at 4, the border b₁ at 2 (2 ≤ 355) and the number fx at the rounds in front of
the border 2, and five of its nine other premises read off the record: hO, hn, ha (K1's
`ownMsgs_index` with `index_alone`, Honest/K1/Law/OwnMsgsIndex.lean: under h and O, of the opening's
messages number 4 alone sits at the index masks' seat; the record's number of the witness's message
is hO's by the library's `P5J.index_at_head`, Johnson/P5J/ReadsTestsAtHead.lean, and the text of
`k4IndexNum`, Honest/K4/Lot/IndexNum.lean) · hfit (the record's field `fits`) · hcov (its field
`hasCoins`: the book's count at the sender's address is the part's). The end is unturned.

WHAT IS LEFT, BESIDE h. K: THE RECORD: twenty fields, OF WHICH THE PROOF SPENDS FOUR (seats, msgs,
fits, hasCoins): whoever wants the tie alone is asked for more than the proof needs; its field
`msgs` is the tie between the Script and the sender's text: it is a premise here, with the record.
O: the library's "opened" at the seated description (under h there is one; it is a letter here
because hP names its base). hP: the job's plan is the opening's at the description's own ground.
hshape, hfreeP: public, between the sending and the verifier's list: premises here; shown under h, O
and hP in AtFullSide/K13/CoinsTieFive.lean. hS: THE STRETCH AT THE BOOK (owner, maskStart + 13, 2
kCol + 1): A PUBLIC TEST THAT HAS NOT RUN AT A BOOK; a closed fact on the maker's list of
stretches at the written description (13 and 37: `rawWantsAtK13_written`,
AtFullSide/K14/RawWantsAtSpenders.lean) IS ITS FORECAST, NOT ITS PAYMENT; StretchAtHead.lean of this
folder carries hS, under h, to "the book is the one that the maker returns" and two public
sentences. hfree: numbers.

Limits. NOT IN FRONT OF A LAW OVER COINS: the ground: the Limits of CoinsTieOfFacts.lean of this
folder. CONDITIONAL ON h AND THE PREMISES NAMED: none is shown here; that they hold together is not
shown. It says no more than its premises: the record holds the tie, hS the book's start. The limits
of CoinsTieAtHead.lean bind here too: the thread stands at the one input w₁ alone; where it holds
nowhere all holds for nothing. THE TIE ALSO HOLDS FOR NOTHING WHERE THE BOOK's LENDING (`lendRow`)
ERRS AT THE KIND's ROW, OR WHERE THE VERIFIER's TAKING DOES NOT RETURN: both stand in front of its
equation (`CoinsTie`, ExchangeAtM3.lean). OF THE TAKING: under h it returns wherever the thread
stands at 355 (`k13_guard_taken`, GuardsAtM3.lean of this folder, at `lettersAt`, of which
`lettersHead` is an instance by its text): so that case is empty at these letters. OF THE LENDING:
no premise here gives it; under h it returns at the book that the maker returns at the head's own
three lists of sendings (`k13_lendRow_at_head`, AtFullSide/K13/LendRowAtHead.lean, where that return
is a premise). `k13_coinsTie_of_seated` is called by the other statement of this file and by
AtFullSide/K13/CoinsTieWritten.lean; that other statement by nothing. This file's imports reach
Johnson/Goal/, by the hypothesis h (`P5J.AtMgA`).

What is not claimed. That any premise holds. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.CoinsTieAtHead
import Johnson.Desc.ProofFile.Honest.K13.StretchAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.OwnMsgsIndex
import Johnson.P5J.ReadsTestsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound (MsgT Mem)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA CellsM TS)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.W (indexFree0)
open ProofFile.Honest.K1 (K1Seated PlaceIn dueR bookCovers)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- THE RECORD IS A PREMISE: no Script is laid. hS (the stretch at the real book: owner, maskStart +
13, 2 kCol + 1) is a public test that has not run at a book; the closed fact on the maker's list
of stretches at the written description (13 and 37) IS ITS FORECAST, NOT ITS PAYMENT.
**`CoinsTie` AT THE HEAD, AT THE BORDER 355, FROM KIND K1's RECORD AT THE OPENING**: an instance of
`k13_coinsTie_of_msgTxt`: n laid at 4; five of its nine premises read off the record `K1Seated`; the
end unturned. CONDITIONAL on h, O, K, hP, hshape, hfreeP, hS and hfree: what each is: the head. -/
theorem k13_coinsTie_of_seated {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {Bs : ProofFile.PureBase} {base₀ : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {blk₂ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : K1.SendJob (PlaceIn ProofFile.Inst) X'} {own₀ : X'} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
    {rad : ℕ → ℕ}
    (K : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 2 blk₂ wit J
      own₀ .opening (P5J.At.arr Zp) seats₀ ms rad)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hshape : (msgsOfChain Zp.made.proof.1)[4]? = some (shapeAt J.P 4))
    (hfreeP : indexFree0 Zp cF ≤ Send.freeMaskEntries (shapeAt J.P 4).maskRows
      (J.P.codes.mask.getD (shapeAt J.P 4).maskCode default).ell (shapeAt J.P 4).answers)
    (hS : ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[355]? =
        some blk →
      oneStretch (rowEntries Bk blk.place 2 0) =
        some (⟨J.P.place, 0⟩, K1.maskStart J.P J.ride 4 + 13, 2 * h.𝔇.P13.lin.kCol + 1))
    (hfree : 13 + (2 * h.𝔇.P13.lin.kCol + 1) ≤ indexFree0 Zp cF) :
    CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 355 weights pile h.𝔇.P13
      (k13ReaderAt h) := by
  obtain ⟨n, hn, ha, e, t⟩ := K1.ownMsgs_index K
  have e' : K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n =
      (P5J.At.N Zp cF).index := by
    rw [← hP]
    exact e
  obtain rfl : n = 4 := K1.index_alone h O (hP ▸ hn) e'
  have hidx : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).N.index = (1, 0) :=
    P5J.index_at_head h.toAtMg
  rw [hidx] at t
  have hcov : bookCovers Bk 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true := by
    unfold bookCovers
    rw [K.hasCoins]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  exact k13_coinsTie_of_msgTxt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ wit J own₀ 4
    (b₁ := 2) (by decide) t hn K.fits hshape ha hfreeP hcov hS hfree

/-- THE RECORD IS A PREMISE: no Script is laid. hW (`bookWhole` RETURNS THE THREAD's BOOK) IS A
PREMISE: that the book which it returns is the thread's is shown nowhere; the closed fact on the
maker's list of stretches at the written description (13 and 37) IS A FORECAST OF h3 AND OF THE
COUNT, NOT THEIR PAYMENT. **`CoinsTie` AT THE HEAD, AT THE BORDER 355, FROM KIND K1's RECORD AT THE
OPENING AND "THE BOOK IS THE MAKER's"**: `k13_coinsTie_of_seated` with its premise hS handed over by
`k13_hS_of_whole` at n = 4. CONDITIONAL on h, O, K, hP, hshape, hfreeP, hW, h1, h3 and hfree: what
each is: the head; h1 and h3: the head of StretchAtHead.lean. -/
theorem k13_coinsTie_of_seated_whole {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {Bs : ProofFile.PureBase} {base₀ : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {blk₂ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : K1.SendJob (PlaceIn ProofFile.Inst) X'} {own₀ : X'} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
    {rad : ℕ → ℕ}
    (K : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 2 blk₂ wit J
      own₀ .opening (P5J.At.arr Zp) seats₀ ms rad)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hshape : (msgsOfChain Zp.made.proof.1)[4]? = some (shapeAt J.P 4))
    (hfreeP : indexFree0 Zp cF ≤ Send.freeMaskEntries (shapeAt J.P 4).maskRows
      (J.P.codes.mask.getD (shapeAt J.P 4).maskCode default).ell (shapeAt J.P 4).answers)
    {p0 p1 p2 : Johnson.G.ChainSends}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 (mergesByName cF.blocksInOrder) = .ok Bk)
    (h1 : ∀ idx, ownerOf indexMaskRun cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx →
      idx.owner = ⟨J.P.place, 0⟩ ∧ idx.base.e = K1.maskStart J.P J.ride 4)
    (h3 : ∀ idx a, ownerOf indexMaskRun cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx →
      linksWants cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
        (mergesByName cF.blocksInOrder).ends (cF.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a →
      a.2 = 13)
    (hfree : 13 + (2 * h.𝔇.P13.lin.kCol + 1) ≤ indexFree0 Zp cF) :
    CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 355 weights pile h.𝔇.P13
      (k13ReaderAt h) :=
  k13_coinsTie_of_seated h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ O K hP hshape hfreeP
    (k13_hS_of_whole h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ J 4 hW h1 h3) hfree

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_coinsTie_of_seated
#print axioms ProofFile.Honest.K13.k13_coinsTie_of_seated_whole
