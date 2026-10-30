-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Rounds.lean: A LIGHT FILE: a challenge found by its round's name
and number. Definitions with code; no theorem. It imports no part, no half and no sending. Its tests
stand in Honest/K2/ToyRounds.lean.

  `roundNumbers`  the numbers, among a chain's rounds, of the rounds of a name
  `drawnAt`       the matrix that a segment's round "RNG" drew; a refusal where the list has no
                  number for the segment, or nothing was heard at that number: for whoever fills
                  the data of a message that hangs on it; in this folder the tests alone call it

Limits. That a segment has just one round "RNG", and that the segments' come in order, is not held
against the table of steps. Nothing on any property.
-/
import Decl.Declared
import Fmt.Rules6Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2

/-- The numbers, among a chain's rounds, of the rounds of a name. -/
def roundNumbers (D : List Fmt.DeclaredRound) (name : String) : List Nat :=
  D.zipIdx.filterMap fun d => if d.1.entry.name == name then some d.2 else none

/-- The matrix that a segment's round "RNG" drew. rng: these rounds' numbers, by segment. -/
def drawnAt (rng : List Nat) (heard : List Fmt.Drawn) (seg : Nat) : Except String (List Int) :=
  match (rng[seg]?).bind (heard[·]?) with
  | some d => .ok d.trits
  | none => .error "a segment's matrix has not been drawn"

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.roundNumbers
#print axioms ProofFile.Honest.K2.drawnAt
