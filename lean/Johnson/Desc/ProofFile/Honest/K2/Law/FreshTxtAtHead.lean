-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshTxtAtHead.lean: the kind "the code switch" (K2): WHICH
COIN STANDS AT AN ENTRY OF THE FOLD's FRESH MASK, BY NUMBER, AT EACH PLACE OF THE KIND's LIST
`switchPlaces`, UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES AND THE OPENING: the three public
premises of `msgTxt_fresh` (Honest/K2/Law/FreshTxt.lean) are paid: one mask row; `NoWord`; the
sending is not empty. Statements with their proofs: joins; no definition.

  `last_in`             the number of the sending's last message lies in the sending
  `lastMaskRows_one`    where the public test `atMostOneMaskRow` accepts and the shared sending's
                        test passes, the sending's last message has just one mask row
  `msgTxt_fresh_of_test`   `msgTxt_fresh` with that test in the stead of "one mask row"
  `msgTxt_fresh_at_head`   UNDER THE HEAD AND THE OPENING, at each place of `switchPlaces`

Why the last message has a mask row at all: a table rides there, and the shared sending's test on a
ride (`K1.rideFits`, Honest/K1/Coins.lean, of other authors) asks that the mask rows be a power of
two: so not 0.

By: `msgTxt_fresh`, `foldAt_last` (FreshTxt.lean) · `maskRows_eq_one`, `atMostOneMaskRow_at_head`
(Honest/K2/Law/OneMaskRowAtHead.lean) · `noWord_open` (Honest/K2/Law/SampledOpen.lean) ·
`shapeFits_of` (Honest/K2/Law/Counts.lean) · `rows_of_laid` (Honest/K2/Law/MaskTxt.lean) ·
`rowsAll_fits` (Honest/K2/Law/Laid.lean) · `notices_size` (Johnson/Top/H0/K2Hands/AtYes.lean): a
switch's sending has 1 + the kept copies + the others.

Limits. That the part is handed its stretches and that the rows are laid stay premises, as returns:
where either fails nothing is said. That the hypothesis on the public files can be met is not said
here. Nothing on the mask row's tail. WHICH COIN IS WRITTEN WHERE: no sentence on what a coin is
for. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.OneMaskRowAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledOpen
import Johnson.Top.H0.K2Hands.AtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- The number of the sending's last message lies in the sending. -/
theorem last_in (p : SwitchPlace) :
    (switchSent p.sizes p.others).size - 1 < (switchSent p.sizes p.others).size := by
  have h := VerifiableInference.Desc.First.K2.notices_size p.sizes.target p.others
  have e : (switchSent p.sizes p.others).size = 1 + p.sizes.target.kept.size + p.others.size := h
  omega

/-- The sending's last message has just one mask row. -/
theorem lastMaskRows_one {p : SwitchPlace} (hp : atMostOneMaskRow p = true)
    (hf : K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others))
      (rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) = true) :
    ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1)
      default).shape.maskRows = 1 := by
  have hn := last_in p
  refine maskRows_eq_one hp hn fun hz => ?_
  have h := (shapeFits_of hf hn).ride p.foldVars (foldAt_last p)
  rw [hz] at h
  simp only [K1.rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩, _⟩ := h
  have h4 : 0 < 2 ^ OnBytes.ceilLog2 0 := Nat.two_pow_pos _
  omega

/-- `msgTxt_fresh` with the public test in the stead of "one mask row". -/
theorem msgTxt_fresh_of_test (ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some c)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) (hp : atMostOneMaskRow p = true) {a : Due}
    (hA : dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) ((switchSent p.sizes p.others).size - 1) = a)
    {q : Nat} (hq : q ≤ 2 * p.foldVars) :
    ∃ x, c.1.eAt (a.e + K1.sig p.foldVars q) = .ok x ∧
      switchMsgTxt ch D readers closing p ((switchSent p.sizes p.others).size - 1) k w hd true 0
        q = some x := by
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  exact msgTxt_fresh ch D readers closing p k w hd hH hV hw
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (last_in p))
    (lastMaskRows_one hp (rowsAll_fits hR)) hA hq

variable {W : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD AND THE OPENING: at each place of the kind's list.** -/
theorem msgTxt_fresh_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
      (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
      (V : Nat → Johnson.Prover.Send.Rows), handed ch p k = some c →
      switchRowsLaid D readers closing p c w hd = .ok V → ∀ q, q ≤ 2 * p.foldVars →
      ∃ x, c.1.eAt ((dueBefore p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) ((switchSent p.sizes p.others).size - 1)).e +
            K1.sig p.foldVars q) = .ok x ∧
        switchMsgTxt ch D readers closing p ((switchSent p.sizes p.others).size - 1) k w hd true 0
          q = some x :=
  fun p hp k w hd _ _ hH hV _ hq =>
    msgTxt_fresh_of_test ch D readers closing p k w hd hH hV (noWord_open O p hp)
      (atMostOneMaskRow_at_head h O p hp) rfl hq

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.last_in
#print axioms ProofFile.Honest.K2.Law.lastMaskRows_one
#print axioms ProofFile.Honest.K2.Law.msgTxt_fresh_of_test
#print axioms ProofFile.Honest.K2.Law.msgTxt_fresh_at_head
