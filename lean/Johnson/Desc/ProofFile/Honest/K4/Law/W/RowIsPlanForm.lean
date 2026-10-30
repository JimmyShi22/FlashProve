-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RowIsPlanForm.lean: TWO DEFINITIONS, NO THEOREM: WHAT IT IS
FOR THE ROW OF THE LAYERS' OWN ROUNDS (kind K4; `k4RowIn`, Honest/K4/Part.lean) TO BE THE ROW INTO
WHICH THE BOOK's MAKER CUTS A SUB-PROTOCOL (`planParts`, Honest/BookEntries.lean): AS MANY PARTS,
AND PART FOR PART THE SAME STATED RUNS OF COINS.

What is here. PUBLIC DATA ALONE: a sub-protocol's place and declared rounds, the maker's list of
merges, K4's public data.

  `K4Counts`: four counts of the plan are not 0: the two long lists of scalars, and the end
      values of the two sumchecks over the tokens.
  `K4RowIsPlan`: ten fields. place, len, row: the sub-protocol stands at K4's place; the maker
      cuts it into as many parts as K4's row has; the last part is m, the others are A. front,
      merge: of these parts the maker's list of merges holds m's address alone. sum, one, pos: m is
      a masked sumcheck with one end value, and some scalar of the row is laid under the segment's
      mask row. noFold: no round of the sub-protocol is a fold's first. states: part for part, the
      runs of coins that K4's part states are the names and counts that the maker lays for the
      plan's part (`partStates`, Honest/Small/SpentOfWants.lean).

Limits. DEFINITIONS: NOTHING IS CLAIMED OF THEM HERE; Law/W/RowIsPlan.lean shows what of the ten
follows from K4's table of rounds. WHAT IS COMPARED: the number of parts (len) and each part's
stated runs (states). THE ROUNDS OF A PART ARE NOT COMPARED BY ANY FIELD: Law/W/CutIsOurs.lean has
that. front AND merge ARE FACTS ON THE LETTER M, the maker's list of merges: nothing compares that
list with the format; Law/W/MergesByName.lean shows both at the list `mergesByName`
(Honest/BookWhole.lean). WHY `K4Counts`: where a part has no scalar of its own the maker lays no
entry, and for a masked sumcheck without end values it lays the "sum" entry and no "ends" entry;
K4's part states a run of count 0 all the same. SO, AT A SUB-PROTOCOL THAT DECLARES K4's ENTRIES,
THE FIELD states IS FALSE WHERE ONE OF THE FOUR COUNTS IS 0 [by reading of the two texts; no theorem
shows it]. Nothing on a book, on coins, or on what a part sends.
No property is claimed.
A LAW's FORM, NOT A PART: no file that defines a part of the proof file's description may import
this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.Small.SpentOfWants
import Johnson.Desc.ProofFile.Honest.BookAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block)

variable {S Cl : Type}

/-- **Four counts of the plan are not 0**: the sums of limb products; the row products; the end
values of the first and of the second sumcheck over the tokens. -/
def K4Counts (Q : K4Pub) : Prop :=
  ledNS Q.P.y.h.xl * Q.P.y.NI ≠ 0 ∧ ledNP Q.P.y.h.xl * Q.P.y.NI ≠ 0 ∧
    ledNO Q.P.y.h.xl * Q.P.y.NI ≠ 0 ∧ nEndT Q.P.y ≠ 0

/-- **K4's row is the maker's row at the sub-protocol b, part for part.** M: the maker's lists of
merges. A, m: the maker's parts: all but the last; the last. -/
structure K4RowIsPlan (M : Merges) (b : Block S Cl) (Q : K4Pub) (A : List PartAt) (m : PartAt) :
    Prop where
  /-- the sub-protocol stands at K4's place -/
  place : b.place = k4Place Q
  /-- as many parts on both sides -/
  len : (planParts b).length = (k4RowIn Q).length
  /-- the merge is the last part -/
  row : planParts b = A ++ [m]
  /-- no part in front of it is listed as a merge -/
  front : ∀ p ∈ A, p.addr ∉ M.ends
  /-- it is -/
  merge : m.addr ∈ M.ends
  /-- it is a masked sumcheck -/
  sum : m.isSum = true
  /-- with one end value -/
  one : m.endScalars = 1
  /-- some scalar of the row is laid under the segment's mask row -/
  pos : ownScalarsOf A + (m.ownScalars - m.endScalars) ≠ 0
  /-- no round of the sub-protocol is a fold's first -/
  noFold : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon"
  /-- part for part: what K4's part states is what the maker lays for the plan's part -/
  states : ∀ (i : Nat) (q : PartAt) (P : Part Unit K4In Unit),
    (planParts b)[i]? = some q → (k4RowIn Q)[i]? = some P →
      P.spends = partStates maskRowRun indexMaskRun (M.ends.contains q.addr) q

end ProofFile.Honest.K4.W
