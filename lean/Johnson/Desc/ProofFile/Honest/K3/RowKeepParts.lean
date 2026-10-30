-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowKeepParts.lean: three small makers of parts, general in the type
of what is passed on: a part that sends nothing, the same with a given second half of its move, and
a part whose last move passes on something else. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a move has two halves (Honest/Frame.lean): `say`, the
message, and `hand`, what is passed on behind the round's challenge.

Why. `quiet` (Honest/K3/Row.lean) is typed at `Unit`. A lookup's row that passes its tables on
(Honest/K3/RowKeep.lean) needs such a part at the row's own state; it lays the tables down at one
stage that sends nothing, and drops them behind its last round.

What is defined.
  `quietLay g`: one move; nothing is sent; `g` says what is passed on.
  `quietAt`: `quietLay` at "what was passed on stays".
  `lastHandMoves g`, `Part.lastHand p g`: the moves of p, the last of which passes on what `g` says.
    All messages, counts, names and stops are those of p. A part without a move stays as it is.

Imported: Honest/Frame.lean.

Users. Honest/K3/RowKeep.lean; Honest/K3/Law/Keep/Bridge.lean.

Limits. Nothing is shown here. That `quietLay`, played alone, shows what `quiet` shows, and that
`Part.lastHand` turns no round of a part that is played alone, is shown in
Honest/K3/Law/Keep/Bridge.lean (`alone_quietLay_quiet`, `alone_lastHand`). `Part.lastHand` is declared
in the namespace of Honest/Frame.lean, so that it can be called behind a dot: a later name of that
file's could clash with it.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {V W X C : Type}

/-- A part of one move that sends nothing. Here g says what is passed on behind the round's
challenge, which the state that g is given holds already. -/
def quietLay (g : State W X → X) : Part V W X :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, g⟩] }

/-- A part of one move that sends nothing and passes on what it was handed. -/
def quietAt : Part V W X := quietLay fun t => t.own

/-- Moves, the last of which passes on what g says. The messages are unchanged. -/
def lastHandMoves (g : State W X → X) : List (Move C W X) → List (Move C W X)
  | [] => []
  | [mv] => [⟨mv.say, g⟩]
  | mv :: mv' :: l => mv :: lastHandMoves g (mv' :: l)

end ProofFile.Honest.K3

namespace ProofFile.Honest

variable {V W X : Type}

/-- A part whose last move passes on what g says. Its counts, names, stops and messages are those of
p. The last move's own second half is not called: g stands in its stead, and is given what the move
in front of the last passed on. -/
def Part.lastHand (p : Part V W X) (g : State W X → X) : Part V W X :=
  { p with moves := K3.lastHandMoves g p.moves }

end ProofFile.Honest
