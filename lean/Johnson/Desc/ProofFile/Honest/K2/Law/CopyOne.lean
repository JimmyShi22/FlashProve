-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyOne.lean: the kind "the code switch" (K2): ONE MESSAGE,
LAID ANEW AT ANOTHER SWITCH OF A CARRIED STRETCH, IS THE MESSAGE THAT ITS SENDER LAID: the same
`messageRows` (Honest/K2/Sending.lean), at the same shape and main rows, at the same elements. Three
statements with their proofs; no definition.

  `cut_through`    a cut of a cut from 0 on is the cut itself
  `copy_one`       NO BOOK: `messageRows` at the stretch that is the sending's cut at `dueBefore`
                   and `messageDue` returns the rows that `rowsAll` laid as message number n
  `copy_carried`   AT TWO SWITCHES p₀ AND p OF ONE CHAIN: UNDER THE BOOK's TIE, three equations on
                   the book's entry number i of what p carries: its owner is p₀'s part; its start is
                   `dueBefore` at message n of p₀'s sending; its count is that message's
                   `messageDue`: `messageRows` at p's carried stretch number i returns p₀'s rows

THE BOOK's TIE IS A PREMISE, ON PUBLIC DATA: it is proved at no book here. THE MAIN ROWS ARE ONE
LETTER M AT BOTH SIDES: that the later switch reckons the sender's main rows anew is not said here.

By: `rowsAll_at` (Honest/K2/Law/MaskCoin.lean) · `stretch_cut_ok`, `stretch_cut_of`
(Honest/K2/Law/Reads.lean) · `carried_of_handed` (Honest/K2/Law/CarriedOfLend.lean) · `cut_within`
(Honest/K2/Law/CarriedWithin.lean) · `own_of_handed` (Honest/K2/Law/MaskTxt.lean).

Limits. An equation at each run's coins: what is WRITTEN where: no sentence on what an element is
for. That both switches are handed their stretches, and that the sender's laying returns, are
premises. One message: nothing on a segment whole. IT IS MEANT FOR A SWITCH p BEHIND p₀; THAT IS NOT
ASKED: one chain's number and one run's coins are all that ties the two. THE LEFT SIDE IS
`segmentGroupRows`' OWN TERM FOR A MESSAGE (Honest/K2/Closing.lean) ONLY OVER TWO BRIDGES THAT ARE NOT IN
THIS FILE: that `foldAt` at the message is `none` (`foldAt_switchFresh`,
Honest/K2/Law/MaskCoin.lean: for all but the last); and that the segment's codes there are the
sender's: typed nowhere yet. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.CarriedWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open Reads

/-- A cut of a cut from 0 on is the cut itself. -/
theorem cut_through {d t : Due} (c : Cs d) {own : Cs t} (h0 : c.cut ⟨0, 0⟩ t = some own)
    {a n : Due} {c' : Cs n} (h : own.cut a n = some c') : c.cut a n = some c' := by
  have g0 := cut_within c ⟨0, 0⟩ t h0
  have g := cut_within own a n h
  have g0f : t.f ≤ d.f := by
    have := g0.1
    simpa using this
  have g0e : t.e ≤ d.e := by
    have := g0.2
    simpa using this
  have gg : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e := ⟨by omega, by omega⟩
  unfold Cs.cut at h0 h ⊢
  rw [dif_pos g0] at h0
  rw [dif_pos g] at h
  rw [dif_pos gg]
  have e0 := Option.some.inj h0
  have e1 := Option.some.inj h
  subst e0
  subst e1
  congr 2
  · funext i
    exact congrArg c.f (Fin.ext (by simp))
  · funext i
    exact congrArg c.e (Fin.ext (by simp))

/-- **NO BOOK.** The sending's cut for message number n, as a stretch, gives that message's rows. -/
theorem copy_one {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)}
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll table codes sent fresh data c = .ok V) {n : Nat} (hn : n < sent.size)
    {s : Stretch}
    (hs : (Stretch.of c).cut (dueBefore codes sent fresh n)
      (messageDue codes (sent.getD n default).shape (foldAt fresh n)) = .ok s) :
    messageRows table codes (sent.getD n default).shape (foldAt fresh n) (data n) s =
      .ok (V n) := by
  obtain ⟨c', hc', hm⟩ := rowsAll_at hV hn
  obtain ⟨c'', hc'', rfl⟩ := stretch_cut_ok hs
  rw [hc'] at hc''
  cases hc''
  exact hm

variable {Bk : ProverCoinCounts}

/-- **UNDER THE BOOK's TIE.** p₀: the sender. p: another switch of the same chain: meant: a later
one; not asked. e: the book's entry number i of what p carries. M: the main rows, one letter at both
sides. -/
theorem copy_carried (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    {M : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) M c₀.1 = .ok V)
    {n : Nat} (hn : n < (switchSent p₀.sizes p₀.others).size) (i : Nat) (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = ⟨p₀.place, 0⟩)
    (t2 : e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) n)
    (t3 : e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD n default).shape
      (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n)) :
    (Stretch.carried p.carries c.2.2 i).bind
        (messageRows freshTable p₀.sizes.codes
          ((switchSent p₀.sizes p₀.others).getD n default).shape
          (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n) (M n)) = .ok (V n) := by
  rw [carried_of_handed ch p k c h i e he, t1, t2, t3]
  obtain ⟨c', hc', hm⟩ := rowsAll_at hV hn
  have ho := own_of_handed ch p₀ k c₀ h₀
  unfold K1.lentCut at ho
  rw [stretch_cut_of (cut_through _ ho hc')]
  exact hm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.cut_through
#print axioms ProofFile.Honest.K2.Law.copy_one
#print axioms ProofFile.Honest.K2.Law.copy_carried
