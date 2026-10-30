-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLOwedLent.lean

It states no goal. No property of the protocol is claimed.

FROM THE ROW's LENDING TO THE SECOND PART's: the
laws on the first chain's closing proximity test lend by `lendRow` at the row of the test's two parts
and read `(restCoins J c.2.1).mem`; `carryRows_of_book` (ClosingWordsBook.lean) speaks of `lendPart` at
the second part and of `stretches q.carries cT.2.2`. They are one. At letters: any job whose members
are `membersL p`. Three theorems; no definition.

  `own_run_of_members`          among what the second part states as carried, number `p.front.length`
                                has the carrying message's own count
  `carryRows_at_row_coins`      the job's text at the coins lent to the row returns message 0 of the
                                switch's lot
  `rows_at_row_coins_are_message_zero`   so whatever it returns there is that message

By what. `lendRow_snd` (K12/CutOfBook.lean); `carryRows_of_book`; the texts of `restPart`,
`restCoins`, `memberRuns` (K12/Parts.lean) and `membersL` (K12/AtProof/JobL.lean).

Hypotheses. hH, hV: the switch's part is handed c and its lot's rows return V at hd. h1: the sending
has two messages. hm: the job's members are `membersL p`. hl: the frame lends the row. hb: the public
test on the book's entries for the two parts (`wordsBookB`).

Limits.
- hb is a premise: at which book it says yes is not said here; LotLBookLine.lean
  (`wordsBookB_at_makers_book`) says it at the maker's book.
- One list of challenges hd on both sides: that the Script's lot and the job read the same is not
  shown here.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `carryRows_at_row_coins` and `rows_at_row_coins_are_message_zero`
bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- k is the theorems' own binder. The letter c stands under hH : `K2.handed ch p k = some c`, which
  names k, and the letter V under hV : `K2.switchRowsLaid … c w … = .ok V`, which names c, a cut of
  k, and w, whose rc holds the committer's coins: premises of the first kind: by their text, at a
  fixed c (a fixed V) they can hold at some values of the coins and fail at others.
- The letter cR stands under hl : `lendRow … (k.look ch) … = .ok cR`, and in the second Rr under ho
  : `carryRows … (restCoins J cR.2.1).mem = .ok Rr`: of the first kind.
- h1, hm and hb speak of the sending's public sizes, of the job's members and of the book's entries:
  they name no coin. w, the run's input, is a letter under no other premise.
- `own_run_of_members` names no coin: it bears none.
- What lifts the bar. For c and V the made terms are what `K2.handed` and `K2.switchRowsLaid`
  return. At the closing place, at the lot's own closing, `switch_lot_returns_at_closing_place`
  (LotLOwedAtHead.lean), from h, hB, hG, hf and hok (the public files, the book, the ground, the
  finish, the closing's public test: no coin), shows, at every k, every list of challenges and every
  w whose instance passes `K2.publicOk`, that both return; `finishIsHanded_at_base`
  (LotLAcceptedFields.lean) shows the first at every k. For cR and Rr none is known to this file. So
  the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingWordsBook
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K2.Law (SwitchCoins)

variable {W₀ Rc Xi Tr X V' : Type} {Bk : ProverCoinCounts}

/-- Among what the second part states as carried, number `p.front.length` has the carrying message's
own count. -/
theorem own_run_of_members (J : TestJob (Local W₀ Rc Xi Tr) X) (p : K2.SwitchPlace)
    (hm : J.members = membersL p) :
    (((restPart J : Part V' (Local W₀ Rc Xi Tr) X).carries[p.front.length]?).map (·.2)) =
      some (K2.messageDue p.sizes.codes (shapeL p) none) := by
  have hlen : (p.front.map fun m => (carriedName m.1 m.2.1 ⟨J.p.place, 1⟩, m.2.2)).length =
      p.front.length := List.length_map _
  have e : memberRuns J ⟨J.p.place, 1⟩ =
      (p.front.map fun m => (carriedName m.1 m.2.1 ⟨J.p.place, 1⟩, m.2.2)) ++
        [(carriedName ⟨p.place, 0⟩ 0 ⟨J.p.place, 1⟩,
          K2.messageDue p.sizes.codes (shapeL p) none)] := by
    unfold memberRuns
    rw [hm]
    unfold membersL
    rw [List.map_append]
    rfl
  show (((memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J])[p.front.length]?).map (·.2)) = _
  rw [e, List.append_assoc, List.getElem?_append_right (le_of_eq hlen), hlen, Nat.sub_self]
  rfl

/-- **The job's text at the coins lent to the row returns message 0 of the switch's lot.** -/
theorem carryRows_at_row_coins {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {ch : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    {V : ℕ → Johnson.Prover.Send.Rows}
    (hH : K2.handed ch p k = some c)
    (hV : K2.switchRowsLaid D readers closing p c w hd = .ok V)
    (h1 : 1 < (K2.switchSent p.sizes p.others).size)
    (J : TestJob (Local W₀ Rc Xi Tr) X) (hm : J.members = membersL p)
    {cR : RowCoins [(firstPart J : Part V' (Local W₀ Rc Xi Tr) X), restPart J]}
    (hl : lendRow Bk (Bk.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part V' (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok cR)
    (hb : wordsBookB Bk ⟨p.place, 0⟩ ⟨J.p.place, 1⟩ p.front.length = true) :
    carryRows D readers closing p w hd (restCoins J cR.2.1).mem = .ok (V 0) :=
  carryRows_of_book hH hV h1
    (ProofFile.Honest.K12.Light.lendRow_snd Bk _ _ J.p.place (firstPart J) (restPart J) cR hl) hb
    (own_run_of_members J p hm)

/-- **So whatever the job's text returns there is that message.** -/
theorem rows_at_row_coins_are_message_zero {D : RowDataOf Xi}
    {readers : Local W₀ Rc Xi Tr → Readers} {closing : K2.Closing} {p : K2.SwitchPlace} {ch : ℕ}
    {k : Coins Bk} {w : Local W₀ Rc Xi Tr} {hd : List Fmt.Drawn}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} {V : ℕ → Johnson.Prover.Send.Rows}
    (hH : K2.handed ch p k = some c)
    (hV : K2.switchRowsLaid D readers closing p c w hd = .ok V)
    (h1 : 1 < (K2.switchSent p.sizes p.others).size)
    (J : TestJob (Local W₀ Rc Xi Tr) X) (hm : J.members = membersL p)
    {cR : RowCoins [(firstPart J : Part V' (Local W₀ Rc Xi Tr) X), restPart J]}
    (hl : lendRow Bk (Bk.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part V' (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok cR)
    (hb : wordsBookB Bk ⟨p.place, 0⟩ ⟨J.p.place, 1⟩ p.front.length = true)
    {Rr : Johnson.Prover.Send.Rows}
    (ho : carryRows D readers closing p w hd (restCoins J cR.2.1).mem = .ok Rr) : Rr = V 0 :=
  Except.ok.inj (ho.symm.trans (carryRows_at_row_coins hH hV h1 J hm hl hb))

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.own_run_of_members
#print axioms ProofFile.Honest.K12.AtProof.carryRows_at_row_coins
#print axioms ProofFile.Honest.K12.AtProof.rows_at_row_coins_are_message_zero
