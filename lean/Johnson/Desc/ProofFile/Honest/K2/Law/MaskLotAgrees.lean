-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MaskLotAgrees.lean: THE MERGE's FIRST LOT `k11MaskLot`
(Honest/K11/Plays/MsgLotsStatement.lean) AND THE SWITCHES' TEXT `switchMsgTxt` AT MESSAGE NUMBER 2
OF THE SWITCH INTO LINK 24 ANSWER ALIKE WHEREVER BOTH ANSWER: UNDER THE LIBRARY's HYPOTHESIS ON THE
PUBLIC FILES, THE OPENING, AND ONE PUBLIC TEST ON THE BOOK. No definition. Lemmas; none of the
library's goals. Joinings: no new argument.

  `senderAt24`       where the switches' text at that message answers at (mask, row 0, place ν), ν
                     below 8192, its answer is element number 439 + ν, of the extension field, of
                     what k (the letter of the type `Coins`) holds at the switch's own address
                     ⟨p.place, 0⟩
  `maskLot_agrees`   the test: the book's first spending entry for ⟨`IM.k11Place`, 1⟩ has the owner
                     ⟨p.place, 0⟩, the start 439 + 3531 in the extension field, and the count 2 lk +
                     2 (`entryRunIs`, Honest/Small/EntryRunIs.lean). Then: wherever the lot at the
                     number `P5J.At.num` Zp 24 0 and the first slot 3531 and the switches' text both
                     answer, they answer alike

How. The first: that it answers gives the two premises on the run and the public instance
(`msgTxt_two_head`, LotsAnswerAtHead.lean of this folder); `msgTxt_mask_row_zero`
(MaskTxtRowZero.lean) at n = 2, its four side premises by `atLink24_gives` (Link24Written.lean);
`cut_eAt` (Reads.lean) at the start ⟨0, 0⟩. The second: `maskLotMeets`
(Honest/K11/Plays/MaskLotOwner.lean) at the letters o := ⟨p.place, 0⟩, base := 439, ν₀ := 3531, L :=
8192; 3531 + (2 lk + 2) ≤ 8192 by lk = 18 (`lkAtFull`, Johnson/Desc/K11/Exchange/LkAtFull.lean).

WITH `num24_at_head` (Link24Written.lean) THE TWO TEXTS STAND AT ONE NUMBER: so the second is,
written out, the clause for this one pair of the frame's hypothesis that lots of one message agree.

WHAT IT IS NOT. That any book passes the test is not said here. Where the frame hands the switch
nothing the switches' text is silent and the second holds of nothing. Beyond 8192 the switches' text
answers with a constant: nothing is said there; the lot's fence ends at 3569. ONE LETTER ch STANDS
FOR BOTH SIDES' CHAIN; at the head's thread the lot stands at that thread's chain. Other spenders'
lots of the same message are not treated: that no entry is spent twice is the book's own test. No
lot is laid.

Limits. The full size; the hypothesis on the public files is taken at the earlier of the format's
two hash functions (`OnBytes.secondHashFunction`). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxtRowZero
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswerAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.Link24Written
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskLotOwner
import Johnson.Desc.K11.Exchange.LkAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.K2.Reads (cut_eAt)
open ProofFile.Honest.K11 (k11MaskLot maskLotMeets)
open Johnson.Desc.First.ForkMerge.Exchange (lkAtFull)

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {rn : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **Where the switches' text answers at (mask, row 0, place ν), it answers with the sender's own
element number 439 + ν.** -/
theorem senderAt24 (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hl : p.link = 24) (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (ν : Nat)
    (y' : Cb.Gl.E) (hν : ν < 8192)
    (hy : switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2 k w hd true 0 ν =
      some y') :
    (k.look ch ⟨p.place, 0⟩).2.eAt (439 + ν) = .ok y' := by
  obtain ⟨-, g2, g3, g4, g5⟩ := atLink24_gives (atLink24_at_head h O p hp) hl
  have hs := msgTxt_two_head h O ch D readers lay hp 2 k w hd true 0 ν
  rw [hy, Option.isSome_some] at hs
  obtain ⟨hH, hv⟩ := Bool.and_eq_true_iff.1 hs.symm
  have t := msgTxt_mask_row_zero h O ch D readers lay hp (n := 2) (by rw [g2]; omega)
    (by rw [g2]; omega) (by rw [g3]; omega) (ν := ν) (by rw [g4]; exact hν) k w hd hH hv
  rw [hy, g5] at t
  obtain ⟨cs, hcs, he⟩ := Option.bind_eq_some_iff.1 t.symm
  have he' : cs.eAt (439 + ν) = .ok y' := by
    cases hx : cs.eAt (439 + ν) with
    | error s =>
      rw [hx] at he
      cases he
    | ok x =>
      rw [hx] at he
      exact congrArg Except.ok (Option.some.inj he)
  have c := cut_eAt hcs he'
  rw [Nat.zero_add] at c
  exact c

/-- **Wherever the merge's first lot and the switches' text both answer, they answer alike.** -/
theorem maskLot_agrees {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Wp Dw rn Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (X : Type) (ch : Nat) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24) (sf : Nat)
    (hE : entryRunIs (spentE Bk ⟨IM.k11Place, 1⟩) 0 ⟨p.place, 0⟩ ⟨sf, 439 + 3531⟩
      ⟨0, 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2⟩ = true)
    (k : Coins Bk) (w : Local W₀ Rc ProofFile.Inst Tr) (hd hd' : List Fmt.Drawn) (mask : Bool)
    (row place : Nat) (y y' : Cb.Gl.E)
    (h1 : (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
      weights (P5J.At.num Zp 24 0) 3531).txt k w hd mask row place = some y)
    (h2 : switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2 k w hd' mask row
      place = some y') : y' = y := by
  have hk := (lkAtFull Wp Dw rn Zp Np cF x h Bs hB).1
  exact maskLotMeets Bk W₀ Rc ProofFile.Inst Tr X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
    weights (P5J.At.num Zp 24 0) 3531 ⟨p.place, 0⟩ sf 439 8192
    (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2) hE
    (by omega)
    (fun k w hd ν y' hν hy => senderAt24 h.toAtMg O ch D readers lay hp hl k w hd ν y' hν hy)
    k w hd hd' mask row place y y' h1 h2

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.senderAt24
#print axioms ProofFile.Honest.K2.Law.maskLot_agrees
