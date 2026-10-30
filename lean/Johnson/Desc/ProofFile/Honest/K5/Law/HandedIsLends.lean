-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/HandedIsLends.lean: WHETHER THE FRAME HANDS A CODE SWITCH's
PART ANYTHING (`K2.handed`, Honest/K2/ScriptLots.lean) IS A TEST WITH CODE ON THE BOOK: THE Bool
`lendsPart` (Honest/Small/LendsRow.lean) AT THE SWITCH's PART. General in the book, the place and
the chain's number. AN EXCHANGE, NOT A PAYMENT: that the Bool is true is proved of no book here.
Three theorems; no definition.

  `handed_isSome`    at every run's letter k: (`K2.handed` ch p k).isSome is that Bool: an equation
  `handed_of_lends`  the Bool is true ⊢ at every run the part is handed something
  `lends_of_handed`  at one run the part is handed something ⊢ the Bool is true

What it is for. The premise "at every run the frame hands the switch's part something" of our forms
on a switch's lots (SwitchAnswers.lean, SendersFillLean.lean, SendersMaskPlan.lean) binds a run's
letter under "for all". By the second theorem it follows from one Bool of the book, the chain's
number, the place and the part's stated counts: no run's letter, no input.

What the Bool asks, by `lendsPart`'s text and `K2.switchPart`'s (Honest/K2/Part.lean: spends := [],
carries := p.carries): the part's own count is the table's at its address; its own cut fits; no
entry that is spent once names the part as its spender; the entries that it carries on meet
p.carries by name and count, in the book's order, and their owners' cuts fit.

By: `lendPart_ok_iff` and `look_dueIs` (Honest/Small/LendsRow.lean).

Limits. ON WHETHER THE PART IS HANDED SOMETHING: NOTHING ON WHAT. The third theorem takes one run's
letter k: whether a book has any is not said. Nothing on whether the part then plays, nor on what it
sends. All limits of LendsRow.lean and of K2/ScriptLots.lean hold.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

variable {Bk : ProverCoinCounts}

/-- **WHETHER THE PART IS HANDED SOMETHING, AT ANY RUN, IS THE BOOK's Bool.** No hypothesis. -/
theorem handed_isSome (ch : Nat) (p : K2.SwitchPlace) (k : Coins Bk) :
    (K2.handed ch p k).isSome = lendsPart Bk (Bk.rowsOf ch) (lookDue Bk ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) := by
  have e : (fun o => (k.look ch o).1) = lookDue Bk ch := funext (look_dueIs k ch)
  have i := lendPart_ok_iff Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries)
  rw [e] at i
  unfold K2.handed
  cases h : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    have n : ¬ lendsPart Bk (Bk.rowsOf ch) (lookDue Bk ch) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
          true :=
      fun g => by
        obtain ⟨c, hc⟩ := i.2 g
        rw [h] at hc
        cases hc
    show false = _
    exact (Bool.eq_false_iff.2 n).symm
  | ok c =>
    show true = _
    exact (i.1 ⟨c, h⟩).symm

/-- **FROM THE BOOK's Bool: AT EVERY RUN THE PART IS HANDED SOMETHING.** CONDITIONAL: hL. -/
theorem handed_of_lends (ch : Nat) (p : K2.SwitchPlace)
    (hL : lendsPart Bk (Bk.rowsOf ch) (lookDue Bk ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) = true) :
    ∀ k : Coins Bk, (K2.handed ch p k).isSome = true :=
  fun k => (handed_isSome ch p k).trans hL

/-- **AND BACK, FROM ONE RUN.** CONDITIONAL: hk. -/
theorem lends_of_handed (ch : Nat) (p : K2.SwitchPlace) (k : Coins Bk)
    (hk : (K2.handed ch p k).isSome = true) :
    lendsPart Bk (Bk.rowsOf ch) (lookDue Bk ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) = true :=
  (handed_isSome ch p k).symm.trans hk

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.handed_isSome
#print axioms ProofFile.Honest.K5.handed_of_lends
#print axioms ProofFile.Honest.K5.lends_of_handed
