-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FieldGuard.lean: a guard around a part that reads the columns
which the frame hands (Seen.opened, Honest/Frame.lean). The frame's text lays on every such part
the duty that at none it errs. A part's text may have no way to err where it reads the field: the
state on entry of a proximity test (TestJob.rec₀, Test.lean) has a type with no room for an error.
So the guard stands around the part: at every move, where the field is none, the error; else the
part as it is. General in the kind. Definitions with code; five theorems.

  fieldWord      the error's words
  Move.needsField, Part.needsField, Placed.needsField   the guard, at a move, a part, a list of
                 parts
  needsField_some, needsField_none   what a guarded move says at some and at none
  needsField_hand   what it passes on
  needsField_length   a guarded part has as many moves
  front_opened   the front that a move lays carries the field of the move's own Seen

What the guard tests is the move's own Seen; a door reads the front. They are one field: moveAt
(Parts.lean) lays s.front i, and Seen.front carries the field on (front_opened).

Limits.
- Where a guarded part is played by run, midAt or midSharedAt, which hand none, it errs at its first
  round: as the frame's limits say, a statement over these behind that round says nothing of such a
  prover. The strategies strat0 and requestStrategy then send fixed substitutes.
- The guard tests that the field is there; nothing on what it holds.
- No property of a prover or a protocol: nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (OpenedColumn)

variable {C V W X : Type}

/-- The words of the error of a guarded move. -/
def fieldWord : String := "a part that reads the opened columns is handed none"

/-- **The guard at a move**: at none the error; else the move as it is. -/
def Move.needsField (mv : Move C W X) : Move C W X :=
  ⟨fun c s t =>
    match s.opened with
    | none => .error fieldWord
    | some _ => mv.say c s t,
    mv.hand⟩

/-- **The guard at a part**: at each of its moves. Its counts, names, stops and shares are its
own. -/
def Part.needsField (p : Part V W X) : Part V W X :=
  { p with moves := p.moves.map Move.needsField }

/-- **The guard at a list of parts at a place.** -/
def Placed.needsField (h : Placed V W X) : Placed V W X :=
  ⟨h.place, h.parts.map Part.needsField⟩

/-- Where the field is some, a guarded move says what the move says. -/
theorem needsField_some (mv : Move C W X) (c : C) (s : Seen) (t : State W X) (cs : List OpenedColumn)
    (h : s.opened = some cs) : mv.needsField.say c s t = mv.say c s t := by
  show (match s.opened with
    | none => (.error fieldWord : Except String Sending)
    | some _ => mv.say c s t) = _
  rw [h]

/-- Where the field is none, a guarded move errs. -/
theorem needsField_none (mv : Move C W X) (c : C) (s : Seen) (t : State W X)
    (h : s.opened = none) : mv.needsField.say c s t = .error fieldWord := by
  show (match s.opened with
    | none => (.error fieldWord : Except String Sending)
    | some _ => mv.say c s t) = _
  rw [h]

/-- It passes on what the move passes on. -/
theorem needsField_hand (mv : Move C W X) : mv.needsField.hand = mv.hand := rfl

/-- **The front that a move lays carries the field of the move's own Seen.** -/
theorem front_opened (s : Seen) (n : Nat) : (s.front n).opened = s.opened := rfl

/-- A guarded part has as many moves. -/
theorem needsField_length (p : Part V W X) : p.needsField.moves.length = p.moves.length :=
  List.length_map _

end ProofFile.Honest

#print axioms ProofFile.Honest.fieldWord
#print axioms ProofFile.Honest.Move.needsField
#print axioms ProofFile.Honest.Part.needsField
#print axioms ProofFile.Honest.Placed.needsField
#print axioms ProofFile.Honest.needsField_some
#print axioms ProofFile.Honest.needsField_none
#print axioms ProofFile.Honest.needsField_hand
#print axioms ProofFile.Honest.needsField_length
#print axioms ProofFile.Honest.front_opened
