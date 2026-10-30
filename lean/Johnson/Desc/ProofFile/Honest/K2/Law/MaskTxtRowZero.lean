-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MaskTxtRowZero.lean: the kind "the code switch" (K2):
`msgTxt_mask_head` (Honest/K2/Law/MaskTxtAtHead.lean) AT ROW 0, PLACE ν: under the library's head
and the opening each message of a place of the list `switchPlaces` has at most one mask row
(`atMostOneMaskRow_at_head`, Honest/K2/Law/OneMaskRowAtHead.lean): so, at a message that has one,
the entry with the format's number ν is the entry at row 0, place ν. One statement with its proof: a
join; no definition.

  `msgTxt_mask_row_zero`   the equation at (row 0, place ν), ν below the mask code's message length

Limits. All Limits of Honest/K2/Law/MaskTxt.lean and MaskTxtAtHead.lean stand. At a message without
a mask row nothing is said. Closed facts by Lean's kernel lie beneath, replayed by no independent
checker. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxtAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.OneMaskRowAtHead

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

/-- **THE EQUATION AT ROW 0, PLACE ν**, under the head and the opening, at a message, not the last,
that has a mask row. -/
theorem msgTxt_mask_row_zero (h : AtMg OnBytes.secondHashFunction Wp Dw rn Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (hl : n ≠ (switchSent p.sizes p.others).size - 1)
    (hm : ((switchSent p.sizes p.others).getD n default).shape.maskRows ≠ 0) {ν : Nat}
    (hν : ν < (p.sizes.codes.mask.getD
      ((switchSent p.sizes p.others).getD n default).shape.maskCode default).ell)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    (hH : (handed ch p k).isSome = true)
    (hv : publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n k w hd true 0 ν =
      (K1.lentCut k ch ⟨p.place, 0⟩
        (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars))).bind fun cs =>
        (cs.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) n + ν)).toOption := by
  have e := maskRows_eq_one (atMostOneMaskRow_at_head h O p hp) hn hm
  have hν' : ν < maskLength p.sizes.codes (switchSent p.sizes p.others) n := by
    unfold maskLength
    rw [e, Nat.one_mul]
    exact hν
  have t := msgTxt_mask_head h O ch D readers lay hp hn hl hν' k w hd hH hv
  rw [e, Nat.mod_one, Nat.div_one] at t
  exact t

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgTxt_mask_row_zero
