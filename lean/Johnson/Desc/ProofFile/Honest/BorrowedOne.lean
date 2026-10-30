-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BorrowedOne.lean: A MATRIX THAT A SEGMENT BORROWS HAS TWO KEYS AT THE
COMMON READER OF THE WITNESS's CELLS (`Cells`, Honest/ForKinds.lean: the segment's number, the
matrix's name as the verifier's own plan lays it, the row, the column): the borrower's segment with
the name in the borrower's list, and the owner's segment with the name in the owner's list. Some
kinds' honest parts ask at the one, some at the other. Here: the owner's key, typed once, off the
public parameters; and, as a premise's form, that the reader answers alike at both. Over the sealed
library and Honest/ForKinds.lean alone. Definitions, tests at made-up entries, and two statements by
unfolding.

  `ownerKey X l M`      under which segment and name, and from which column on, the entry M of
                       segment l's list is its owner's: a borrowed one (`TMat.kind` = 1): the
                       layers' segment of the group `aId / 256 - 1`, the name of entry
                       `aId % 256` of that segment's list ("" beyond it), `ttOff`; every other
                       one: (l, its own name, 0). `ownerKeyBy`: the same of two letters
  `lastSegment X`       the head's segment's number
  `BorrowedOne X c`     at every entry of the list of every segment up to that one, at all rows
                       and columns: the reader's answer under the segment's own number and the
                       entry's own name is its answer at `ownerKey`
  `ownerKey_own`        at an entry that is not borrowed the key is the segment's own
  `borrowedOne_iff`     so the premise speaks of the borrowed entries alone

WHICH ENTRIES ARE BORROWED, by the plans' text: "xbI" in a layers' segment from the second group on
(OnBytes/Model/LayerPlan.lean), "qa" in an attention segment (AttentionPlan.lean), "xbL" in the head
(HeadPlan.lean); `ttOff` is 0 in all three, and the maker of the smallness test's shapes refuses
another (`HTailF2.shapeF`, OnBytes/Model/Tail.lean). THE LIBRARY's KIN: `OrdsN.seamFF`, `seamA`,
`seamH` (Johnson/Meaning/Lists.lean): the same three equations on lists of integer matrices, by list
numbers.

Limits. A premise's form: nothing shows it of any reader. Nothing holds `ownerKey` against a layout
or a committed table. Nothing on a run, a coin or a measure. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Model (TMat HTailF2)
open VerifiableInference.Desc.First.Look (tlAt)

/-- The owner's key, of: how many segments a group of layers has; the segments' lists. -/
def ownerKeyBy (step : Nat) (tl : Nat → Option HTailF2) (l : Nat) (M : TMat) :
    Nat × String × Nat :=
  if M.kind == 1 then
    (step * (M.aId / 256 - 1),
      (((tl (step * (M.aId / 256 - 1))).bind (·.mats[M.aId % 256]?)).map (·.name)).getD "", M.ttOff)
  else (l, M.name, 0)

/-- **The owner's key**, off the public parameters. -/
def ownerKey (X : OnBytes.Model.Verify.Public) (l : Nat) (M : TMat) : Nat × String × Nat :=
  ownerKeyBy (if X.p4 then 2 else 1) (tlAt X) l M

/-- The head's segment's number: the last segment's (the library's `isHead`,
Johnson/Desc/First/Look/K3Own.lean, and `tlAt` count so). -/
def lastSegment (X : OnBytes.Model.Verify.Public) : Nat := (if X.p4 then 2 else 1) * X.NGr

/-- **A borrowed matrix answers under the borrower's key as under its owner's**, at the segments up
to the head's. A premise's form. -/
def BorrowedOne (X : OnBytes.Model.Verify.Public) (c : Cells) : Prop :=
  ∀ (l a : Nat) (M : TMat), l ≤ lastSegment X → (tlAt X l).bind (·.mats[a]?) = some M → ∀ r k,
    c.cell l M.name r k =
      c.cell (ownerKey X l M).1 (ownerKey X l M).2.1 r ((ownerKey X l M).2.2 + k)

theorem ownerKey_own (X : OnBytes.Model.Verify.Public) (l : Nat) {M : TMat} (h : M.kind ≠ 1) :
    ownerKey X l M = (l, M.name, 0) := by
  unfold ownerKey ownerKeyBy
  rw [if_neg (by simpa using h)]

/-- The premise speaks of the borrowed entries alone. -/
theorem borrowedOne_iff (X : OnBytes.Model.Verify.Public) (c : Cells) :
    BorrowedOne X c ↔ ∀ (l a : Nat) (M : TMat), l ≤ lastSegment X →
      (tlAt X l).bind (·.mats[a]?) = some M → M.kind = 1 → ∀ r k, c.cell l M.name r k =
        c.cell (ownerKey X l M).1 (ownerKey X l M).2.1 r ((ownerKey X l M).2.2 + k) := by
  constructor
  · intro h l a M hl hM _ r k
    exact h l a M hl hM r k
  · intro h l a M hl hM r k
    by_cases hk : M.kind = 1
    · exact h l a M hl hM hk r k
    · rw [ownerKey_own X l hk, Nat.zero_add]

/-! ### Tests at made-up entries -/

/-- Made-up lists: segment 4 has the entries "a", "b"; no other segment has a list. -/
def toyLists (l : Nat) : Option HTailF2 :=
  if l == 4 then some { mats := #[{ name := "a" }, { name := "b" }] } else none

-- not borrowed: the segment's own key
#guard ownerKeyBy 2 toyLists 5 { name := "ah", aId := 1500 } == (5, "ah", 0)
-- borrowed of the group 2 (aId / 256 = 3), entry 1: two segments a group: segment 4, "b"
#guard ownerKeyBy 2 toyLists 5 { name := "qa", kind := 1, aId := 3 * 256 + 1 } == (4, "b", 0)
-- one segment a group: segment 2, which has no list here: ""; an entry beyond the list: ""
#guard ownerKeyBy 1 toyLists 5 { name := "xbI", kind := 1, aId := 3 * 256 + 1 } == (2, "", 0)
#guard ownerKeyBy 2 toyLists 5 { name := "qa", kind := 1, aId := 3 * 256 + 2 } == (4, "", 0)
-- the first column is handed on
#guard ownerKeyBy 2 toyLists 5 { name := "qa", kind := 1, aId := 3 * 256, ttOff := 7 } ==
  (4, "a", 7)

end ProofFile.Honest

#print axioms ProofFile.Honest.ownerKey_own
#print axioms ProofFile.Honest.borrowedOne_iff
