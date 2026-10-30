-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/OwnOfRounds.lean: NO HYPOTHESIS. Definitions, statements and
proofs. No definition and no statement here names a kind. By the writers of the feed-forward layers'
own rounds. It imports Honest/BookRowKit.lean and Honest/BookCutsLaw.lean: files of other writers.

What is here. PUBLIC DATA ALONE: names of rounds and counts. A round's scalars are "own" unless the
round's name stands in `frameNames` (`scalarsIn`, `frameNames`, `partsCut`: Honest/BookOf.lean). THE
CUT OF A SUB-PROTOCOL's ROUNDS INTO PARTS LOSES NO ROUND's SCALARS: the own scalars of its parts
(`ownScalarsOf`, `partsInFront`: Honest/BookRowKit.lean; `planParts`, `stretchesBy`,
`PartAt.ownScalars`: Honest/BookEntries.lean), added up, are the own scalars of its declared rounds,
added up round by round. So `ownScalarsOf` of `partsInFront` is a sum with one term for each
sub-protocol. TWO LAWS OF OTHER WRITERS ARE CALLED: `partsCut_sum` (Honest/BookCutsLaw.lean): the
cut adds up to the number of rounds; `BookRow.ownScalarsOf_cons` (Honest/BookRowKit.lean). And the
library's `OnBytes.foldl_add` (OnBytes/Chain/Lists.lean).

  `ownOfPairs`, `foldl_ownPairs`, `ownOfPairs_append`: the own scalars of a list of rounds, each
      a name and a number: `PartAt.ownScalars` without the address.
  `own_stretches`: over consecutive stretches of a list they add up to those of the list's front
      as far as the stretches reach.
  `ownScalarsOf_numbered`: the own scalars of a list of stretches that are numbered and laid as
      parts at one place.
  `ownOfRounds`, `ownScalarsOf_planParts`: **THE STATEMENT.**
  `ownScalarsOf_append`, `ownScalarsOf_blocks`, `ownScalarsOf_partsInFront`: so for a list of
      sub-protocols, and for `partsInFront`.

Kin. `foldl_own` (Honest/BookRowKit.lean) and `foldl_add_shift` (Honest/BookCutsLaw.lean) are sums
from any start, as `foldl_ownPairs` is. `stretchesBy_flatten` (Honest/K4/Law/W/PlanRow.lean) and
`sumsBy_rows` (Honest/K4/Law/TableFitsRows.lean) are similar tools; these two files are no part of
the library yet.

Not shown here. Nothing on which names are a segment's own: `frameNames` is taken as it stands. In
`ownScalarsOf_partsInFront` the segment's number l and the place a are free of each other, as in
`partsInFront`: where a is no place of segment l the whole segment is taken. Nothing on any
sub-protocol's rounds. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit
import Johnson.Desc.ProofFile.Honest.BookCutsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

/-! ## 1 The own scalars of a list of rounds -/

/-- The own scalars of a list of rounds, each a name and a number of scalars: the fold of
`PartAt.ownScalars`, without the address. -/
def ownOfPairs (u : List (String × Nat)) : Nat :=
  u.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) 0

/-- The fold from any start a is a plus the fold from 0. -/
theorem foldl_ownPairs : ∀ (u : List (String × Nat)) (a : Nat),
    u.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) a = a + ownOfPairs u
  | [], _ => rfl
  | r :: u, a => by
    show List.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) a (r :: u) =
      a + List.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) 0 (r :: u)
    rw [List.foldl_cons, List.foldl_cons,
      foldl_ownPairs u (if frameNames.contains r.1 then a else a + r.2),
      foldl_ownPairs u (if frameNames.contains r.1 then 0 else 0 + r.2)]
    by_cases hc : frameNames.contains r.1 = true
    · rw [if_pos hc, if_pos hc]
      omega
    · rw [if_neg hc, if_neg hc]
      omega

/-- The own scalars of two lists laid end to end add up. -/
theorem ownOfPairs_append (u w : List (String × Nat)) :
    ownOfPairs (u ++ w) = ownOfPairs u + ownOfPairs w := by
  show (u ++ w).foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) 0 = _
  rw [List.foldl_append, foldl_ownPairs w]
  rfl

/-! ## 2 Stretches -/

/-- Over consecutive stretches of a list the own scalars add up to those of the list's front, as far
as the stretches reach. -/
theorem own_stretches : ∀ (ks : List Nat) (l : List (String × Nat)),
    ((stretchesBy l ks).map ownOfPairs).sum = ownOfPairs (l.take ks.sum)
  | [], _ => rfl
  | k :: ks, l => by
    show (ownOfPairs (l.take k) :: (stretchesBy (l.drop k) ks).map ownOfPairs).sum =
      ownOfPairs (l.take (k :: ks).sum)
    rw [List.sum_cons, List.sum_cons, own_stretches ks (l.drop k), List.take_add,
      ownOfPairs_append]

/-- The own scalars of a list of stretches, numbered from k on and laid as parts at one place, are
the stretches' own scalars added up. -/
theorem ownScalarsOf_numbered (a : Place) : ∀ (L : List (List (String × Nat))) (k : Nat),
    ownScalarsOf ((L.zipIdx k).map fun x => (⟨⟨a, x.2⟩, x.1⟩ : PartAt)) =
      (L.map ownOfPairs).sum
  | [], _ => rfl
  | u :: L, k => by
    rw [List.zipIdx_cons, List.map_cons, BookRow.ownScalarsOf_cons,
      ownScalarsOf_numbered a L (k + 1), List.map_cons, List.sum_cons]
    rfl

/-! ## 3 The statement -/

variable {S Cl : Type}

/-- The own scalars of a sub-protocol's declared rounds, round by round. -/
def ownOfRounds (b : Block S Cl) : Nat :=
  b.rounds.foldl (fun n r => if frameNames.contains r.entry.name then n else n + scalarsIn r) 0

/-- **THE OWN SCALARS OF A SUB-PROTOCOL's PARTS ARE THOSE OF ITS DECLARED ROUNDS.** No hypothesis.
-/
theorem ownScalarsOf_planParts (b : Block S Cl) : ownScalarsOf (planParts b) = ownOfRounds b := by
  unfold planParts
  rw [ownScalarsOf_numbered, own_stretches, List.take_of_length_le]
  · unfold ownOfPairs ownOfRounds
    rw [List.foldl_map]
  · have h := (partsCut_sum b).1
    rw [OnBytes.foldl_add] at h
    rw [List.length_map]
    omega

/-- The own scalars of two lists of parts laid end to end add up. -/
theorem ownScalarsOf_append : ∀ (A C : List PartAt),
    ownScalarsOf (A ++ C) = ownScalarsOf A + ownScalarsOf C
  | [], C => by
    show ownScalarsOf C = 0 + ownScalarsOf C
    omega
  | q :: A, C => by
    rw [List.cons_append, BookRow.ownScalarsOf_cons, BookRow.ownScalarsOf_cons,
      ownScalarsOf_append A C]
    omega

/-- Over a list of sub-protocols: one term for each. -/
theorem ownScalarsOf_blocks : ∀ bs : List (Block S Cl),
    ownScalarsOf (bs.flatMap planParts) = (bs.map ownOfRounds).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, ownScalarsOf_append, ownScalarsOf_planParts, ownScalarsOf_blocks bs,
      List.map_cons, List.sum_cons]

/-- **`partsInFront`: one term for each sub-protocol that it takes.** No hypothesis. -/
theorem ownScalarsOf_partsInFront (bs : List (Block S Cl)) (l : Nat) (a : Place) :
    ownScalarsOf (partsInFront bs l a) =
      (((bs.filter fun b => b.place.link == some l).takeWhile fun b =>
        b.place != a).map ownOfRounds).sum :=
  ownScalarsOf_blocks _

end ProofFile.Honest

#print axioms ProofFile.Honest.foldl_ownPairs
#print axioms ProofFile.Honest.ownOfPairs_append
#print axioms ProofFile.Honest.own_stretches
#print axioms ProofFile.Honest.ownScalarsOf_numbered
#print axioms ProofFile.Honest.ownScalarsOf_planParts
#print axioms ProofFile.Honest.ownScalarsOf_append
#print axioms ProofFile.Honest.ownScalarsOf_blocks
#print axioms ProofFile.Honest.ownScalarsOf_partsInFront
