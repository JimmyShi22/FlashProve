-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/MarksList.lean: THE MARKS OF THE ATTENTION SEGMENTS' OWN ROUNDS
(kind K5) AT THE PROOF FILE's FIRST CHAIN, AS ONE LIST. One definition; no theorem. NO PROPERTY IS
CLAIMED BY THE DEFINITION. EACH share IN IT IS A WRITTEN PAIR OF NUMBERS AND NO BOUND.

What it is for. The frame's law on the first chain takes the owners' marks as one list (`FirstAsks`,
Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean, its argument hm), the kinds' lists in a row.
Whoever names a kind's list imports its file: so this file stands over what the definition's code
reads and nothing more; the lemmas on it stand in
Johnson/Desc/ProofFile/Honest/K5/Law/MarksListLaw.lean.

Why the two marks are written out. They are `mkReads`
(Johnson/Desc/ProofFile/Honest/K5/Law/MarkReads.lean) and `mkLive` (MarkLive.lean beside it); these
two files also hold laws that stand over much more. `k5Marks_eq` (MarksListLaw.lean) says, by
unfolding alone, that the list is the list of these two: if one of the texts drifts, that file no
longer compiles. THE PIN HOLDS ONLY WHERE THAT FILE IS BUILT: a build of this file alone does not
see a drift.

Limits. A list. No sentence on a measure stands here. What the tests mean, and what a mark's silence
gives: the two marks' own files.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.K5.Honest.Law.MarkTest
import Johnson.Desc.K5.Honest.Law.LiveMark
import Johnson.Desc.ProofFile.Lot.K5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (readRounds speaks liveRounds speaksL)

set_option linter.unusedVariables false in
/-- **The marks of the attention segments' own rounds at the first chain**, read off the ground as
the kind's lot reads it: the places from `H2K5.k5Places G₀`, the plan of a place's group from
`G₀.W.A`. Two marks a place: first the one on the challenges that two tables' weights are made of,
then the one on the challenges that a slot's coefficient is made of: `mkReads` and `mkLive` written
out. None where the group has no plan: in scope that does not happen (`k5Marks_open`,
Johnson/Desc/ProofFile/Honest/K5/Law/MarksListLaw.lean). A mark is laid wherever the group has a
plan, also where the lot's own tests on a seat would lay no half. Zp is not read: it stands for the
form that all kinds' lists share. EACH share IS A WRITTEN PAIR OF NUMBERS AND NO BOUND. No property
is claimed. -/
def k5Marks (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) : List Mark :=
  (H2K5.k5Places G₀).flatMap fun y =>
    match G₀.W.A[y.2.2]? with
    | some a =>
      [{ place := ⟨1, some y.1, 3, .K5⟩
         test := fun _ own =>
           if speaks a.own (Att.P.parCOf a).geo own then
             some "a challenge that two tables' weights are made of is 0 or 1"
           else none
         share := ⟨2 * (readRounds a.own (Att.P.parCOf a).geo).length * (2 ^ 128 + 1) ^ 3,
           Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ },
       { place := ⟨1, some y.1, 3, .K5⟩
         test := fun _ own =>
           if speaksL a.own own then some "a challenge that a slot's coefficient is made of is 0"
           else none
         share := ⟨1 * (liveRounds a.own).length * (2 ^ 128 + 1) ^ 3,
           Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ }]
    | none => []

end ProofFile.Honest.K5
