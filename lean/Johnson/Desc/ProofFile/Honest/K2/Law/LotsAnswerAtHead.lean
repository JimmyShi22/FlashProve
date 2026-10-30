-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LotsAnswerAtHead.lean: the kind "the code switch" (K2): WHERE
THE TEXTS OF THE KIND's LOTS ANSWER (Honest/K2/Law/LotsAnswer.lean), UNDER THE LIBRARY's HEAD, AT
EACH OF THE PLAN's PLACES OF THE KIND: THE PREMISE `closingOk` OF THAT FILE's LAWS IS PAID; AND
THREE OF THE FIVE THAT `switchMsgTxt`'s ANSWERING HANGS ON ARE PAID TOO: TWO ARE LEFT. Five
statements with their proofs: corollaries; no definition.

  `msgTxt_isSome_head`   whether `switchMsgTxt` answers: the five, by name
  `msgTxt_public_head`   THE SAME AT ALL ENTRIES, CHALLENGES AND COINS, AND AT INPUTS WITH ONE
                         PUBLIC INSTANCE
  `msgTxt_answers_head`  where the five hold it answers
  `msgTxt_two_head`      WHETHER IT ANSWERS, UNDER THE HEAD: TWO LEFT: whether the frame hands the
                         part its stretches, and `publicOk` at the input's public instance
  `msgTxt_answers_two`   where these two hold it answers

By: `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean): under the head `closingOk` says yes at
each place of `switchPlaces`: by closed facts of Lean's kernel, under a raised depth and a lifted
limit on heartbeats · `serves_at_head`, `roomy_at_head`, `fits_at_head`
(Honest/K2/Law/PublicAtHead.lean): under the head `Sizes.serves`, `Sizes.roomy` and `placeFits` say
yes at each place of `switchPlaces`: by closed facts of Lean's kernel at the written places.

Limits. All Limits of Honest/K2/Law/LotsAnswer.lean stand but the one on `closingOk`: ON WHETHER A
TEXT ANSWERS: NOTHING ON WHAT IT ANSWERS; at `lotClosingAt` at the plan's own segments alone (the
layout is a letter); THAT THE TWO THAT ARE LEFT HOLD IS SHOWN HERE AT NO BOOK AND NO INPUT. The head
and the opening are hypotheses. NO LOT IS LAID. The closed facts beneath are replayed by no
independent checker. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {rn : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **Whether `switchMsgTxt` answers, under the head.** -/
theorem msgTxt_isSome_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (n : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r j : Nat) :
    (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd mask r
        j).isSome =
      ((handed ch p k).isSome && (p.sizes.serves && p.sizes.roomy &&
        publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x && placeFits p)) :=
  msgTxt_isSome ch D readers lay (segmentsOf Zp Bs.G₀) p (closing_at_head h O p hp) n k w hd mask
    r j

/-- **THE SAME AT ALL ENTRIES, CHALLENGES AND COINS, AND AT INPUTS WITH ONE PUBLIC INSTANCE, UNDER
THE HEAD.** -/
theorem msgTxt_public_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    (n n' : Nat) (k k' : Coins Bk) (w w' : Local W₀ Rc Xi Tr) (hx : w.x = w'.x)
    (hd hd' : List Fmt.Drawn) (mask mask' : Bool) (r r' j j' : Nat) :
    (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd mask r
        j).isSome =
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n' k' w' hd' mask' r'
        j').isSome :=
  msgTxt_public ch D readers lay (segmentsOf Zp Bs.G₀) p (closing_at_head h O p hp) n n' k k' w w'
    hx hd hd' mask mask' r r' j j'

/-- **Where the five hold it answers, under the head.** -/
theorem msgTxt_answers_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (n : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r j : Nat)
    (hh : (handed ch p k).isSome = true) (hs : p.sizes.serves = true)
    (hr : p.sizes.roomy = true)
    (hv : publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true)
    (hf : placeFits p = true) :
    ∃ y, switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd mask r j =
      some y :=
  msgTxt_answers ch D readers lay (segmentsOf Zp Bs.G₀) p (closing_at_head h O p hp) n k w hd mask
    r j hh hs hr hv hf

/-- **WHETHER IT ANSWERS, UNDER THE HEAD: TWO LEFT.** -/
theorem msgTxt_two_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (n : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r j : Nat) :
    (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd mask r
        j).isSome =
      ((handed ch p k).isSome && publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x) := by
  rw [msgTxt_isSome_head h O ch D readers lay hp, serves_at_head h O p hp, roomy_at_head h O p hp,
    fits_at_head h O p hp, Bool.true_and, Bool.true_and, Bool.and_true]

/-- **Where these two hold it answers, under the head.** -/
theorem msgTxt_answers_two (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (n : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (r j : Nat)
    (hh : (handed ch p k).isSome = true)
    (hv : publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    ∃ y, switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd mask r j =
      some y :=
  msgTxt_answers_head h O ch D readers lay hp n k w hd mask r j hh (serves_at_head h O p hp)
    (roomy_at_head h O p hp) hv (fits_at_head h O p hp)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgTxt_isSome_head
#print axioms ProofFile.Honest.K2.Law.msgTxt_public_head
#print axioms ProofFile.Honest.K2.Law.msgTxt_answers_head
#print axioms ProofFile.Honest.K2.Law.msgTxt_two_head
#print axioms ProofFile.Honest.K2.Law.msgTxt_answers_two
