-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MaskTxtAtHead.lean: the kind "the code switch" (K2):
`msgTxt_mask` (Honest/K2/Law/MaskTxt.lean) UNDER THE LIBRARY's HEAD AND THE OPENING, AT A PLACE OF
THE LIST `switchPlaces`, AT THE LOT's OWN CLOSING: THE EQUATION WITHOUT THE PREMISE THAT THE TEXT
ANSWERS: in its stead two things, by name: that the frame hands the part its stretches; `publicOk`
at the input's public instance. And: there the number lies below the part's count. Two statements
with their proofs: joins; no definition.

  `msgTxt_mask_head`      the equation
  `msgTxt_mask_in_head`   the number lies below the count: no premise but the head and the opening

By: `msgTxt_two_head` (Honest/K2/Law/LotsAnswerAtHead.lean) · `fits_at_head`
(Honest/K2/Law/PublicAtHead.lean).

Limits. All Limits of Honest/K2/Law/MaskTxt.lean stand. THE HEAD AND THE OPENING ARE HYPOTHESES AND
MAY BE UNMET. That the two hold is proved at no book and no input. Closed facts by Lean's kernel lie
beneath, replayed by no independent checker. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswerAtHead

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

/-- **THE EQUATION, UNDER THE HEAD, WITHOUT THE PREMISE THAT THE TEXT ANSWERS.** -/
theorem msgTxt_mask_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (hl : n ≠ (switchSent p.sizes p.others).size - 1) {ν : Nat}
    (hν : ν < maskLength p.sizes.codes (switchSent p.sizes p.others) n) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (hH : (handed ch p k).isSome = true)
    (hv : publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd true
        (ν % ((switchSent p.sizes p.others).getD n default).shape.maskRows)
        (ν / ((switchSent p.sizes p.others).getD n default).shape.maskRows) =
      (K1.lentCut k ch ⟨p.place, 0⟩
        (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars))).bind fun cs =>
        (cs.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) n + ν)).toOption :=
  msgTxt_mask ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p hn hl hν k w hd
    (by rw [msgTxt_two_head h O ch D readers lay hp, hH, hv]; rfl)

/-- **THE NUMBER LIES BELOW THE PART's COUNT**, under the head and the opening. -/
theorem msgTxt_mask_in_head (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (hl : n ≠ (switchSent p.sizes p.others).size - 1) :
    ∀ ν : Nat, ν < maskLength p.sizes.codes (switchSent p.sizes p.others) n →
      maskBase p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) n + ν <
        (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)).e :=
  msgTxt_mask_in p (fits_at_head h O p hp) hn hl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgTxt_mask_head
#print axioms ProofFile.Honest.K2.Law.msgTxt_mask_in_head
