-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Answers.lean: WHAT THE TWO FILES' TESTS ON THE SILENT ROUNDS' PLAIN PARTS
(silK, silP, OnBytes/Flat/FilesAt.lean) GIVE THE PRINTER: the front's answers are the typed record's
own answers as the printer writes them, the joining round repeats them, and the key file's copy's
number is 0.

Main names.
  ansL_eq     ansL rec, the list against which both tests hold the answers, IS (trAns rec.2).map
    E.ofTriple: entry for entry (trAns, OnBytes/Flat/LinkSib.lean: the list that the printer writes
    into the parsed files).
  silK_gives  where the key file's test says yes.
  silP_gives  where the proof file's test says yes.

Why. The printed form comes back only if the key file's front bears the key's record's answers, and
the joining round the front's (the clauses ansT, copyT of what the form's way back asks; the clause
answers of Printable, OnBytes/Prover/Print/Carrier.lean). An accepted transcript has passed these
tests: so these clauses need no premise on a strategy.

Does not show: that a transcript is accepted. The proof file's test does not read the copy's number.
Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.FilesAt
import OnBytes.Flat.LinkSib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open OnBytes.Flat OnBytes.Slice OnBytes.Maker

variable {v lg s : ℕ}

/-- **The list against which the tests hold the answers is the list that the printer writes.** -/
theorem ansL_eq (rec : RecP NZ v lg s) : ansL rec = (trAns rec.2).map OnBytes.E.ofTriple := by
  unfold ansL keyOf trAns
  rw [List.map_ofFn, Array.toList_ofFn]
  rfl

theorem silK_gives (rec : RecP NZ v lg s) (f : FrontMsg (List OnBytes.E))
    (j : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t : ByteArray)
    (h : silK rec f j t = true) :
    f.answers = (trAns rec.2).map OnBytes.E.ofTriple ∧ f.copy = 0 ∧ j.answers = f.answers := by
  unfold silK silentOf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1.trans (ansL_eq rec), h2, h3.trans h1.symm⟩

theorem silP_gives {X : Type} (z : X × RecP NZ v lg s) (f : FrontMsg (List OnBytes.E))
    (j : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t : ByteArray)
    (h : silP z f j t = true) :
    f.answers = (trAns z.2.2).map OnBytes.E.ofTriple ∧ j.answers = f.answers := by
  obtain ⟨h1, h2⟩ := silP_answers z f j t h
  exact ⟨h1.trans (ansL_eq z.2), h2.trans h1.symm⟩

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.ansL_eq
#print axioms OnBytes.Prover.Print.silK_gives
#print axioms OnBytes.Prover.Print.silP_gives
