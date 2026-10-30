-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Rows.lean: THE TABLE's ITEM "rows" BEHIND THE LAST CHAIN's FIRST BLOCK,
IN THE MEANING IN WHICH THE OWN TEST's ROW CLOSES IT ("what the seat's way in returns of the chain's
own record: every open row of its group holds of the words"), GIVES RowsHold
(Johnson/Desc/Third/Law/Row0.lean), which row 0's law spends: at the seat's own way in, enterOwn
(Johnson/Desc/K12/Seat/Own.lean). One definition with code, theorems.

OBJECT   enterOwn: it never refuses, and lays the record's statement and own group's number as they
         are (by rfl).
USER     the field rows of RowZeroLeft (Johnson/Desc/Third/Law/Row0AtTable.lean), at the filling
         rowsOpen … enterOwn … of ML (Johnson/Flat/Last/LastAtArm.lean
         [not in this library]): its body is
         rowsHold_of_enterOwn's premise at mOf t := wordsOn t.st (tabAt cs arr (seatOwn s) t.st w).
LETTERS  ρ · mOf : the test's own record → words.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  allSay_of_open       every place's OpenSays gives AllSay of the group's open rows.
  ownT                 what enterOwn returns.   enterOwn_eq: by rfl.
  rowsHold_of_enterOwn   **the link**: no premise beside "rows" itself.
What is not claimed. Where the own group is not there RowsHold holds of every words: row 0's law
does not lean on that corner: behind the block's yes the group is there and (Dot) is its last open
row (Says). Nothing on soundness.

-/
import Johnson.Desc.Means.Items
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.Third.Law.Row0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes
open OnBytes.Means (Words OpenSays AllSay rowAt_iff)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- Every place's OpenSays gives AllSay of the group's open rows. -/
theorem allSay_of_open (T : Statement) (g : Nat) (G : OnBytes.Group) (hG : T.groups[g]? = some G)
    (m : Words K) (h : ∀ i, OpenSays ρ T g i m) : AllSay ρ T G.rows.toList m := by
  intro r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  exact h i r (rowAt_iff.2 ⟨G, hG, by rw [← Array.getElem?_toList]; exact hi⟩)

/-- What the seat's way in returns of the chain's own record. -/
def ownT (s : S₃) : T12 :=
  { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
    mask := s.loc.mask }

theorem enterOwn_eq (s : S₃) : enterOwn s = .ok (ownT s) := rfl

/-- **"rows", as the own test's row closes it, gives RowsHold.** -/
theorem rowsHold_of_enterOwn (s : S₃) (mOf : T12 → Words K)
    (h : ∃ t, enterOwn s = .ok t ∧ ∀ i, OpenSays ρ t.st t.g i (mOf t)) :
    RowsHold ρ s (mOf (ownT s)) := by
  obtain ⟨t, ht, hs⟩ := h
  obtain rfl : ownT s = t := Except.ok.inj ht
  exact fun G hG => allSay_of_open ρ s.st s.loc.own G hG _ hs

end VerifiableInference.Desc.Third.Law
