-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/StepToy.lean: controls of Johnson/Desc/Step.lean: the fold of a table of steps,
evaluated at toys (`#guard`).

Main names.
  `idle k`: a step that tests nothing and takes k columns. `rv0`, `rvP p`: a round in which nothing
    was sent or drawn; one that drew the position p. `v31`: a view of three rounds `rv0` and one
    opened column. `v3p`: three rounds that differ.
  `add`, `isSum`: steps on a state that is a number: add the stretch's positions; test the sum. `key
    k`: take one column if its key is k. `any`: the last test that says yes to every state. The
    tests. A yes. The seven ways to a no, each alone: the table is empty; a stretch is short; a step
    refuses; a step says that it took more columns than are left; a round alone is left over; a
    column alone is left over; the last test says no. `chainRun` says as `chainSay` at six of these.
    The state is threaded and each row is handed its own stretch, in order (a wrong order and a
    wrong cut are refused). A row over no round. `chainEnd` hands out the last state. Each column
    goes to one step, in order. AT SIZE: 500 rows of 100 rounds, and 50,000 rows of one round. Just
    as many columns as are left can be taken; one more cannot. AND THE TWO LIMITS THAT Step.lean's
    HEAD TELLS: a step can take a column unread; a step can read a column and not take it, so that a
    later step reads it again.

Limits: toys. No step of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.StepToy

/-- A step that tests nothing and says that it took k columns. -/
def idle {S : Type} (k : Nat) : Step S := fun s _ _ => some (s, k)

/-- A round in which nothing was sent or drawn. -/
def rv0 : Fmt.RoundView := ⟨[], ⟨[], [], [], none⟩⟩

/-- A round that drew the position p. -/
def rvP (p : Nat) : Fmt.RoundView := ⟨[], ⟨[], [p], [], none⟩⟩

/-- A view of three rounds `rv0` and one opened column. -/
def v31 : Fmt.View := ⟨[rv0, rv0, rv0], [(0, 0, [])]⟩

/-- A view of three rounds that differ; no column. -/
def v3p : Fmt.View := ⟨[rvP 1, rvP 10, rvP 100], []⟩

/-- Add the stretch's positions to the state. -/
def add : Step Nat := fun s rs _ =>
  some (rs.foldl (fun a r => r.drawn.poss.foldl (· + ·) a) s, 0)

/-- Test the state; take nothing. -/
def isSum (n : Nat) : Step Nat := fun s _ _ => if s = n then some (s, 0) else none

/-- A step that takes one column if its key is k, and refuses otherwise. -/
def key (k : Nat) : Step Unit := fun s _ c =>
  if (c.head?.map (·.1)) == some k then some (s, 1) else none

/-- The last test that says yes to every state. -/
def any {S : Type} : S → Bool := fun _ => true

/-! a yes, and the ways to a no, each alone -/
#guard chainSay (S := Unit) [⟨"a", 2, idle 1⟩, ⟨"b", 1, idle 0⟩] () any v31 == "yes"
#guard chainSay (S := Unit) [] () any ⟨[], []⟩ == "no: the table of stretches is empty"
#guard chainSay (S := Unit) [⟨"a", 2, idle 1⟩, ⟨"b", 2, idle 0⟩] () any v31 ==
  "no: refused at b: the stretch is short"
#guard chainSay (S := Unit) [⟨"a", 2, fun _ _ _ => none⟩, ⟨"b", 1, idle 0⟩] () any v31 ==
  "no: refused at a"
#guard chainSay (S := Unit) [⟨"a", 2, idle 2⟩, ⟨"b", 1, idle 0⟩] () any v31 ==
  "no: refused at a: it took more columns than are left"
#guard chainSay [⟨"a", 3, add⟩] 0 (fun s => s == 110) v3p ==
  "no: the last state fails the last test"
#guard chainSay [⟨"a", 3, add⟩] 0 (fun s => s == 111) v3p == "yes"
#guard chainSay (S := Unit) [⟨"a", 2, idle 1⟩] () any v31 == "no: left over: 1 rounds, 0 columns"
#guard chainSay (S := Unit) [⟨"a", 3, idle 0⟩] () any v31 == "no: left over: 0 rounds, 1 columns"
#guard chainRun (S := Unit) [⟨"a", 2, idle 1⟩, ⟨"b", 1, idle 0⟩] () any v31
#guard !chainRun (S := Unit) [] () any ⟨[], []⟩
#guard !chainRun (S := Unit) [⟨"a", 2, idle 1⟩, ⟨"b", 2, idle 0⟩] () any v31
#guard !chainRun (S := Unit) [⟨"a", 2, idle 2⟩, ⟨"b", 1, idle 0⟩] () any v31
#guard !chainRun (S := Unit) [⟨"a", 2, idle 1⟩] () any v31
#guard !chainRun (S := Unit) [⟨"a", 3, idle 0⟩] () any v31

/-! the state is threaded; each row is handed its own stretch, in order -/
#guard chainRun [⟨"a", 1, add⟩, ⟨"is 1", 0, isSum 1⟩, ⟨"b", 1, add⟩, ⟨"is 11", 0, isSum 11⟩,
  ⟨"c", 1, add⟩, ⟨"is 111", 0, isSum 111⟩] 0 any v3p
#guard chainSay [⟨"a", 1, add⟩, ⟨"is 10", 0, isSum 10⟩, ⟨"b", 2, add⟩] 0 any v3p ==
  "no: refused at is 10"
#guard chainSay [⟨"a", 2, add⟩, ⟨"is 1", 0, isSum 1⟩, ⟨"b", 1, add⟩] 0 any v3p ==
  "no: refused at is 1"
#guard (chainEnd [⟨"a", 3, add⟩] 5 any v3p).toOption == some 116

/-! at size -/
#guard chainRun (S := Unit) (List.replicate 500 ⟨"r", 100, idle 0⟩) () any
  ⟨List.replicate 50000 rv0, []⟩
#guard chainRun (S := Unit) (List.replicate 50000 ⟨"r", 1, idle 0⟩) () any
  ⟨List.replicate 50000 rv0, []⟩

/-! each column goes to one step, in order: a step that looks at the first column handed to it -/
#guard chainRun [⟨"first", 1, key 7⟩, ⟨"second", 1, key 8⟩] () any
  ⟨[rv0, rv0], [(7, 0, []), (8, 0, [])]⟩
#guard !chainRun [⟨"first", 1, key 7⟩, ⟨"again", 1, key 7⟩] () any
  ⟨[rv0, rv0], [(7, 0, []), (8, 0, [])]⟩

/-! the limits: a step that takes a column unread; a step that reads a column and does not take it
-/
#guard chainRun (S := Unit) [⟨"unread", 3, idle 1⟩] () any v31
#guard chainRun [⟨"looks", 1, fun s r c => (key 7 s r c).map fun p => (p.1, 0)⟩,
  ⟨"again", 1, key 7⟩, ⟨"second", 0, key 8⟩] () any ⟨[rv0, rv0], [(7, 0, []), (8, 0, [])]⟩

/-! just as many columns as are left can be taken; one more cannot -/
#guard chainRun (S := Unit) [⟨"a", 2, idle 2⟩] () any ⟨[rv0, rv0], [(7, 0, []), (8, 0, [])]⟩
#guard !chainRun (S := Unit) [⟨"a", 2, idle 3⟩] () any ⟨[rv0, rv0], [(7, 0, []), (8, 0, [])]⟩
#guard !chainRun (S := Unit) [⟨"a", 2, idle 1⟩] () any ⟨[rv0, rv0], []⟩

end VerifiableInference.Desc.StepToy
