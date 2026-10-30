-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SharedAheadWritten.lean: AT THE LIBRARY's WRITTEN DESCRIPTION OF
THE PROOF FILE AT THE FULL SIZE (P2Law.ProofPlan.WP, Johnson/AtFull/ProofPlan/WP.lean) AND ITS
WRITTEN LIST OF THE SHARED CHAIN's SENDINGS (Johnson.G.proofSendsFull.2.1,
Johnson/G/SendsWritten.lean) THE FRAME's sharedAhead (Honest/BookShared.lean) RETURNS, AND WHAT IT
RETURNS IS A WRITTEN LIST OF FOURTEEN ENTRIES: A FACT ON WRITTEN VALUES, by Lean's kernel; THAT ANY
DESCRIPTION HAS THESE ROUNDS OR THIS CUT IS NO THEOREM HERE. Definitions with code and statements,
each with its proof.

  aheadView, aheadView_inj   an entry as a tuple of its six fields (the frame's Ahead derives no
                  test of equality); two entries with one tuple are one
  writtenShort    **the fourteen entries, written**
  shortIs, short_test   the test with code: sharedAhead returns, and its list's tuples are the given
                  ones; it accepts writtenShort's
  sharedAhead_written   **THE EQUATION**: sharedAhead WP proofSendsFull.2.1 = .ok writtenShort
  short_bites     **THE TEST CAN FAIL**: one letter of one name bent; one number bent by one; the
                  last entry lacking; two entries in the other order: each is rejected
  short_counts    fourteen; four with the owner at "send o_u", nine at "send o_omega", one at a fold
                  of the shared chain; of each of the two sendings' coins just one entry spends
  short_at_u, short_at_omega   the entries at these two owners, written out

How. String.splitOn does not reduce in the kernel: sharedAhead and the four definitions through
which it reads a sending's label are unfolded by name and the library's Johnson.Unfolds.splitOn_eq
(Johnson/Unfolds/SplitOn.lean) is rewritten under them; then one evaluation. (The recipe:
Honest/K14/SwitchLabels.lean.) No option is raised.

Limits. BY ITSELF IT GIVES NO MEMBER OF ANY STATEMENT UNDER THE LIBRARY's HEAD: it wants a law that
carries the answer from one description to another that is alike (Honest/BookSharedAlike.lean), and
the tie of the head's description to WP (Honest/K14/WrittenAtHead.lean);
Honest/K14/SharedAheadAtHead.lean joins them. It says that sharedAhead returns and what; NOT that a
book's own tests pass, nor that the whole book's maker returns: sharedAhead is a second text of a
part of two definitions of the frame's, and no maker of a book calls it. WP's own limit stands: its
values were printed off the goals' stored full-size public files by Lean's evaluator. If the text of
sharedAhead, foldEntries, sentIn, isSwitch or testOf turns so that the value or the unfolding turns,
this file stops compiling. Of WP the first chain is not read. Nothing on what is or is not hidden;
no property.
-/
import Johnson.Desc.ProofFile.Honest.BookShared
import Johnson.AtFull.ProofPlan.WP
import Johnson.G.SendsWritten
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- An entry as a tuple of its six fields. -/
def aheadView (e : Ahead) : String × Addr × Due × Due × Addr × Bool :=
  (e.name, e.owner, e.start, e.count, e.spender, e.once)

/-- Two entries with one tuple are one. -/
theorem aheadView_inj : Function.Injective aheadView := by
  rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h
  simp only [aheadView, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- **The fourteen entries, written**: name; owner; start; count; the part that is handed the run;
true: spent, false: carried. -/
def writtenShort : List Ahead :=
  [
    ⟨"the fold's fresh mask to 2.-.9.0: fold",
      ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10808⟩, ⟨0, 15⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, true⟩,
    ⟨"the split's mask message to 2.-.8.0: split",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩, ⟨⟨2, none, 8, .K14⟩, 0⟩, true⟩,
    ⟨"message 0 of 2.-.2.0 to 2.-.9.0: carried",
      ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false⟩,
    ⟨"message 1 of 2.-.5.0 to 2.-.9.0: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false⟩,
    ⟨"message 0 of 2.-.2.0 to 2.-.9.1: carried",
      ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false⟩,
    ⟨"message 1 of 2.-.5.0 to 2.-.9.1: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false⟩,
    ⟨"message 1 of 2.-.2.0 to 2.-.9.1: carried",
      ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10808⟩, ⟨0, 167⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false⟩,
    ⟨"message 0 of 2.-.5.0 to 2.-.10.0: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩, false⟩,
    ⟨"message 1 of 2.-.5.0 to 2.-.10.0: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩, false⟩,
    ⟨"message 0 of 2.-.5.0 to 2.-.10.1: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false⟩,
    ⟨"message 1 of 2.-.5.0 to 2.-.10.1: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false⟩,
    ⟨"message 0 of 2.-.5.0 to 3.-.2.0: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
    ⟨"message 0 of 2.-.5.0 to 3.-.2.1: carried",
      ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
    ⟨"message 0 of 2.-.10.0 to 2.-.10.1: carried",
      ⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false⟩]

/-- **The test**: sharedAhead returns at the written description and sendings, and its list's tuples
are the given ones. -/
def shortIs (t : List (String × Addr × Due × Due × Addr × Bool)) : Bool :=
  match sharedAhead WP proofSendsFull.2.1 with
  | .ok l => decide (l.map aheadView = t)
  | .error _ => false

/-- It accepts the written list's tuples. -/
theorem short_test : shortIs (writtenShort.map aheadView) = true := by
  simp only [shortIs, sharedAhead, foldEntries, sentIn, isSwitch, testOf,
    Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- **THE EQUATION: AT THE WRITTEN DESCRIPTION AND THE WRITTEN SENDINGS THE FRAME's sharedAhead
RETURNS THE WRITTEN LIST.** -/
theorem sharedAhead_written : sharedAhead WP proofSendsFull.2.1 = .ok writtenShort := by
  have h := short_test
  unfold shortIs at h
  cases hs : sharedAhead WP proofSendsFull.2.1 with
  | error w =>
    rw [hs] at h
    cases h
  | ok l =>
    rw [hs] at h
    exact congrArg Except.ok (List.map_injective_iff.2 aheadView_inj (of_decide_eq_true h))

/-- **THE TEST CAN FAIL**: one letter of the last name bent; the first entry's start bent by one;
the last entry lacking; the first two entries in the other order. -/
theorem short_bites :
    shortIs ((writtenShort.map aheadView).dropLast ++
      [("message 0 of 2.-.10.0 to 2.-.10.1: carrieD",
        ⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false)]) = false ∧
    shortIs (("the fold's fresh mask to 2.-.9.0: fold",
        ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10809⟩, ⟨0, 15⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, true) ::
      (writtenShort.map aheadView).drop 1) = false ∧
    shortIs (writtenShort.map aheadView).dropLast = false ∧
    shortIs (((writtenShort.map aheadView).take 2).reverse ++
      (writtenShort.map aheadView).drop 2) = false := by
  simp only [shortIs, sharedAhead, foldEntries, sentIn, isSwitch, testOf,
    Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- Fourteen entries; four with the owner at "send o_u", nine at "send o_omega", one at a fold of
the shared chain; of each of the two sendings' coins just one entry spends. -/
theorem short_counts : writtenShort.length = 14 ∧
    (writtenShort.filter fun e => e.owner == ⟨⟨2, none, 2, .K1⟩, 0⟩).length = 4 ∧
    (writtenShort.filter fun e => e.owner == ⟨⟨2, none, 5, .K1⟩, 0⟩).length = 9 ∧
    (writtenShort.filter fun e => e.owner == ⟨⟨2, none, 10, .K12⟩, 0⟩).length = 1 ∧
    (writtenShort.filter fun e => e.once && e.owner == ⟨⟨2, none, 2, .K1⟩, 0⟩).length = 1 ∧
    (writtenShort.filter fun e => e.once && e.owner == ⟨⟨2, none, 5, .K1⟩, 0⟩).length = 1 := by
  decide +kernel

/-- The four entries whose owner is the part at "send o_u". -/
theorem short_at_u :
    (writtenShort.filter fun e => e.owner == ⟨⟨2, none, 2, .K1⟩, 0⟩).map aheadView =
     [
      ("the fold's fresh mask to 2.-.9.0: fold",
        ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10808⟩, ⟨0, 15⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, true),
      ("message 0 of 2.-.2.0 to 2.-.9.0: carried",
        ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false),
      ("message 0 of 2.-.2.0 to 2.-.9.1: carried",
        ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false),
      ("message 1 of 2.-.2.0 to 2.-.9.1: carried",
        ⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨0, 10808⟩, ⟨0, 167⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false)] := by
  decide +kernel

/-- The nine entries whose owner is the part at "send o_omega". -/
theorem short_at_omega :
    (writtenShort.filter fun e => e.owner == ⟨⟨2, none, 5, .K1⟩, 0⟩).map aheadView =
     [
      ("the split's mask message to 2.-.8.0: split",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩, ⟨⟨2, none, 8, .K14⟩, 0⟩, true),
      ("message 1 of 2.-.5.0 to 2.-.9.0: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false),
      ("message 1 of 2.-.5.0 to 2.-.9.1: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false),
      ("message 0 of 2.-.5.0 to 2.-.10.0: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩, false),
      ("message 1 of 2.-.5.0 to 2.-.10.0: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩, false),
      ("message 0 of 2.-.5.0 to 2.-.10.1: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false),
      ("message 1 of 2.-.5.0 to 2.-.10.1: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false),
      ("message 0 of 2.-.5.0 to 3.-.2.0: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨3, none, 2, .K12⟩, 0⟩, false),
      ("message 0 of 2.-.5.0 to 3.-.2.1: carried",
        ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩, false)] := by
  decide +kernel

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.aheadView_inj
#print axioms ProofFile.Honest.K14.short_test
#print axioms ProofFile.Honest.K14.sharedAhead_written
#print axioms ProofFile.Honest.K14.short_bites
#print axioms ProofFile.Honest.K14.short_counts
#print axioms ProofFile.Honest.K14.short_at_u
#print axioms ProofFile.Honest.K14.short_at_omega
