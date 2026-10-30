-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MaskTxt.lean: the kind "the code switch" (K2): WHAT
`switchMsgTxt` (Honest/K2/ScriptLots.lean) ANSWERS AT AN ENTRY OF A MESSAGE's MASK ROWS, for every
message of a switch but the last: wherever it answers, it answers the element with the number
`maskBase` + ν OF THE PART's OWN CUT, ν the format's number of the entry. Four statements with their
proofs: joins; no definition.

  `own_of_handed`   what `handed` hands as the part's own IS `K1.lentCut` at the part's address and
                    count
  `rows_of_laid`    where `switchRowsLaid` returns, its rows are `rowsAll`'s at the part's own cut
  `msgTxt_mask`     THE EQUATION, OF OPTIONS, AT EVERY RUN's COINS, under one premise: that the text
                    answers at that entry
  `msgTxt_mask_in`  under the public test `placeFits`: that number lies below the part's count

THE RIGHT SIDE NAMES THE CUT (`K1.lentCut` at ⟨p.place, 0⟩ and the sending's count) AND A NUMBER
MADE OF PUBLIC DATA: neither the input nor the challenges. WHETHER THE TEXT ANSWERS is another
matter: `msgTxt_isSome`, `msgTxt_two_head` (Honest/K2/Law/LotsAnswer.lean, LotsAnswerAtHead.lean):
it hangs on the book's test and on public tests, one of them at the input's public instance.

NO DEFAULT: the cut's reader `Cs.eAt` refuses beyond the count, and the right side is then `none`;
`msgTxt_mask_in` says that under `placeFits` the number is not beyond it.

By: `rowsAll_mask`, `foldAt_switchFresh` (Honest/K2/Law/MaskCoin.lean) · `maskEntry_in_fits`
(Honest/K2/Law/MaskFits.lean) · `cut_of_lend` (Honest/K1/ScriptAtLaw.lean, of other authors). Near:
the like at the shared sending's own text, by those authors.

Limits. WHAT IS WRITTEN WHERE: no sentence on what an entry is for. NOT AT THE LAST MESSAGE, the
next fold's mask, whose table rides. The map from an entry to the number is one to one within one
message, by its form; ACROSS MESSAGES, and against the numbers that tails, pads and main rows take,
NOTHING IS SAID HERE. That a spender's row is handed the same elements is not said here. ν is the
format's number of an entry: row ν % m at place ν / m, m the message's mask rows. NO LOT IS LAID.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskFits
import Johnson.Desc.ProofFile.Honest.K2.Law.PlanAsks
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type}

/-- What `handed` hands as the part's own is the cut, by name. -/
theorem own_of_handed (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c) :
    K1.lentCut k ch ⟨p.place, 0⟩
      (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) = some c.1 := by
  unfold handed at h
  cases hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    rw [hl] at h
    cases h
  | ok c' =>
    rw [hl] at h
    have ec : c' = c := Option.some.inj h
    subst ec
    exact K1.cut_of_lend (Bk.rowsOf ch) k ch ⟨p.place, 0⟩ _ c' hl

/-- Where `switchRowsLaid` returns, its rows are `rowsAll`'s, at some main rows, at the own cut. -/
theorem rows_of_laid (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w h = .ok V) :
    ∃ M, rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) M c.1 = .ok V := by
  unfold switchRowsLaid at hV
  split at hV
  · cases hV
  · split at hV
    · cases hV
    · obtain ⟨M, -, hR⟩ := exBind_ok hV
      exact ⟨M, hR⟩

/-- **THE EQUATION.** Wherever the text answers at the entry with the format's number ν of the mask
rows of message number n, not the last, it answers the element number `maskBase` + ν of the part's
own cut. Take `msgTxt_mask_in` with it. ON THE OTHER ARM: where hA fails the text is `none`: the
frame's `Script.ofLots` (Honest/Thread/ScriptLots.lean) then lays at that entry what another lot of
the message's number answers, and, where none does, the constant 0, which is no element of a cut.
WHETHER hA HOLDS: by `msgTxt_public` (Honest/K2/Law/LotsAnswer.lean), at the lot's own closing,
under the public test `closingOk`: the same at all entries, challenges and coins, and at inputs with
one public instance. -/
theorem msgTxt_mask (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) {n : Nat} (hn : n < (switchSent p.sizes p.others).size)
    (hl : n ≠ (switchSent p.sizes p.others).size - 1) {ν : Nat}
    (hν : ν < maskLength p.sizes.codes (switchSent p.sizes p.others) n) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn)
    (hA : (switchMsgTxt ch D readers closing p n k w h true
      (ν % ((switchSent p.sizes p.others).getD n default).shape.maskRows)
      (ν / ((switchSent p.sizes p.others).getD n default).shape.maskRows)).isSome = true) :
    switchMsgTxt ch D readers closing p n k w h true
        (ν % ((switchSent p.sizes p.others).getD n default).shape.maskRows)
        (ν / ((switchSent p.sizes p.others).getD n default).shape.maskRows) =
      (K1.lentCut k ch ⟨p.place, 0⟩
        (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars))).bind fun cs =>
        (cs.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) n + ν)).toOption := by
  unfold switchMsgTxt at hA ⊢
  cases hh : handed ch p k with
  | none =>
    rw [hh] at hA
    cases hA
  | some c =>
    rw [hh] at hA
    rw [own_of_handed ch p k c hh]
    cases hV : switchRowsLaid D readers closing p c w h with
    | error e =>
      have hA' : ((switchRowsLaid D readers closing p c w h).toOption.map fun V =>
          K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) true
            (ν % ((switchSent p.sizes p.others).getD n default).shape.maskRows)
            (ν / ((switchSent p.sizes p.others).getD n default).shape.maskRows)).isSome = true := hA
      rw [hV] at hA'
      cases hA'
    | ok V =>
      obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w h hV
      have hm := rowsAll_mask hR hn (foldAt_switchFresh p.sizes p.others p.foldVars hl) hν
      show ((switchRowsLaid D readers closing p c w h).toOption.map fun V =>
          K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) true
            (ν % ((switchSent p.sizes p.others).getD n default).shape.maskRows)
            (ν / ((switchSent p.sizes p.others).getD n default).shape.maskRows)) =
        (c.1.eAt (maskBase p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) n + ν)).toOption
      rw [hV, hm]
      rfl

/-- **THE NUMBER LIES BELOW THE PART's COUNT**, under the public test. -/
theorem msgTxt_mask_in (p : SwitchPlace) (hf : placeFits p = true) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (hl : n ≠ (switchSent p.sizes p.others).size - 1) :
    ∀ ν : Nat, ν < maskLength p.sizes.codes (switchSent p.sizes p.others) n →
      maskBase p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) n + ν <
        (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)).e :=
  maskEntry_in_fits hf hn (foldAt_switchFresh p.sizes p.others p.foldVars hl)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.own_of_handed
#print axioms ProofFile.Honest.K2.Law.rows_of_laid
#print axioms ProofFile.Honest.K2.Law.msgTxt_mask
#print axioms ProofFile.Honest.K2.Law.msgTxt_mask_in
