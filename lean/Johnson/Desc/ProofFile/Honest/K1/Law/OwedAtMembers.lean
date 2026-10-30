-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/OwedAtMembers.lean: THE SHARED "SENDING" (the kind K1): WHAT
ProofFile's FORWARD ROWS (FirstRows.rows, Honest/Thread/FirstRows.lean) OWE AT K1's 51 NUMBERS IN THE
SEGMENTS, AT THE LIBRARY's TWO WRITTEN LISTS (P5J.At.links, P5J.At.ps). PUBLIC: closed lists. Ten
theorems; no definition.

  - owed_two_full, owed_reads_full, owed_digits_full: THREE CLOSED TESTS, each an evaluation in
    Lean's kernel (decide +kernel; no compiled code): every item that the row owes at number 2 is
    one of pin 0 0, pinI, row 0 (sample 0) · at each "reads" (K1.noL l false, l below 25): one of
    pin l 1, row l (sample 1), tie l, forms l j n at the (j, n) of earlyRuns (IM.subAt l); OR it is
    pin l 0 or constr l small AND IS OPEN IN FRONT OF THE MEMBER · at each "digits" (K1.noL l true):
    one of pin l 2, row l (sample 2).
  - owed_two_no, owed_reads_no, owed_digits_no: THREE CONTROLS: each test with one allowed item
    struck (pinI; tie l; row l (sample 2)) says no: the two over the 25 segments: at one l at least.
  - owed_two, owed_reads, owed_digits: what the tests' yes gives, item by item.
  - k1Ix_lt: IM.k1Ix l d < IM.nAt l: so K1.noL l d is one of the numbers 14 * l + i + 2, i <
    IM.nAt l, by which ProofFile's gather asks.

For whom. SharesAtMembers.lean.

Limits. THE FULL SIZE's TWO WRITTEN LISTS ALONE. The tests say that the row owes NOTHING ELSE; that
it owes each of these is not said here. They count nothing. THE SIX EVALUATIONS TOGETHER COST ABOUT
A MINUTE OF A BUILD (two calls that built this file and nothing else took 67 and 75 seconds whole,
on one box). It stands over files of L25's that are on no seal. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.K1.Law.LaterOne
import Johnson.IMR.LinkSeat
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item earlyRuns start)

/-- **AT NUMBER 2 THE ROW OWES NOTHING ELSE.** -/
theorem owed_two_full : ((FirstRows.rows P5J.At.links P5J.At.ps 2).owes.all fun j =>
    [Item.pin 0 0, Item.pinI, Item.row 0 (.sample 0)].contains j) = true := by
  decide +kernel

/-- A control: with pinI struck the test says no. -/
theorem owed_two_no : ((FirstRows.rows P5J.At.links P5J.At.ps 2).owes.all fun j =>
    [Item.pin 0 0, Item.row 0 (.sample 0)].contains j) = false := by
  decide +kernel

/-- **AT EACH "reads" THE ROW OWES NOTHING ELSE**: but pin l 0 and constr l small, which are open in
front of the member. -/
theorem owed_reads_full : ((List.range 25).all fun l =>
    (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l false)).owes.all fun j =>
      ([Item.pin l 1, Item.row l (.sample 1), Item.tie l] ++
        (earlyRuns (IM.subAt l)).map fun x => Item.forms l x.1 x.2).contains j ||
      ((j == Item.pin l 0 || j == Item.constr l .small) &&
        (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
          (K1.noL l false)).contains j)) = true := by
  decide +kernel

/-- A control: with tie l struck the test says no. -/
theorem owed_reads_no : ((List.range 25).all fun l =>
    (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l false)).owes.all fun j =>
      ([Item.pin l 1, Item.row l (.sample 1)] ++
        (earlyRuns (IM.subAt l)).map fun x => Item.forms l x.1 x.2).contains j ||
      ((j == Item.pin l 0 || j == Item.constr l .small) &&
        (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
          (K1.noL l false)).contains j)) = false := by
  decide +kernel

/-- **AT EACH "digits" THE ROW OWES NOTHING ELSE.** -/
theorem owed_digits_full : ((List.range 25).all fun l =>
    (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l true)).owes.all fun j =>
      [Item.pin l 2, Item.row l (.sample 2)].contains j) = true := by
  decide +kernel

/-- A control: with row l (sample 2) struck the test says no. -/
theorem owed_digits_no : ((List.range 25).all fun l =>
    (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l true)).owes.all fun j =>
      [Item.pin l 2].contains j) = false := by
  decide +kernel

/-- What owed_two_full's yes gives. -/
theorem owed_two {j : Item} (hj : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps 2).owes) :
    j = Item.pin 0 0 ∨ j = Item.pinI ∨ j = Item.row 0 (.sample 0) := by
  have hb := List.all_eq_true.1 owed_two_full j hj
  simpa using hb

/-- What owed_reads_full's yes gives. -/
theorem owed_reads {l : ℕ} (hl : l < 25) {j : Item}
    (hj : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l false)).owes) :
    (j = Item.pin l 1 ∨ j = Item.row l (.sample 1) ∨ j = Item.tie l ∨
        ∃ x ∈ earlyRuns (IM.subAt l), j = Item.forms l x.1 x.2) ∨
      ((j = Item.pin l 0 ∨ j = Item.constr l .small) ∧
        j ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
          (K1.noL l false)) := by
  have hb := List.all_eq_true.1 (List.all_eq_true.1 owed_reads_full l (List.mem_range.2 hl)) j hj
  rcases (Bool.or_eq_true _ _).mp hb with h1 | h2
  · left
    have h1' := List.mem_append.1 (List.contains_iff_mem.1 h1)
    rcases h1' with h3 | h3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
      rcases h3 with h3 | h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr (Or.inl h3))
    · obtain ⟨x, hx, e⟩ := List.mem_map.1 h3
      exact Or.inr (Or.inr (Or.inr ⟨x, hx, e.symm⟩))
  · right
    obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h2
    refine ⟨?_, List.contains_iff_mem.1 h4⟩
    rcases (Bool.or_eq_true _ _).mp h3 with h5 | h5
    · exact Or.inl (beq_iff_eq.1 h5)
    · exact Or.inr (beq_iff_eq.1 h5)

/-- What owed_digits_full's yes gives. -/
theorem owed_digits {l : ℕ} (hl : l < 25) {j : Item}
    (hj : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l true)).owes) :
    j = Item.pin l 2 ∨ j = Item.row l (.sample 2) := by
  have hb := List.all_eq_true.1 (List.all_eq_true.1 owed_digits_full l (List.mem_range.2 hl)) j hj
  simpa using hb

/-- K1's numbers are among those by which the gather asks. -/
theorem k1Ix_lt (l : ℕ) (d : Bool) : IM.k1Ix l d < IM.nAt l := by
  unfold IM.nAt IM.k1Ix
  cases d <;> by_cases e : l = 24 <;> simp [e]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.owed_two_full
#print axioms ProofFile.Honest.K1.owed_two_no
#print axioms ProofFile.Honest.K1.owed_reads_full
#print axioms ProofFile.Honest.K1.owed_reads_no
#print axioms ProofFile.Honest.K1.owed_digits_full
#print axioms ProofFile.Honest.K1.owed_digits_no
#print axioms ProofFile.Honest.K1.owed_two
#print axioms ProofFile.Honest.K1.owed_reads
#print axioms ProofFile.Honest.K1.owed_digits
#print axioms ProofFile.Honest.K1.k1Ix_lt
