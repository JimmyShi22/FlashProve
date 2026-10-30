-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SigmaBatStatement.lean: A MARKER ON A LIST OF A PLAN's ENTRIES, AND A LAW ON IT:
GENERAL: of the library it names the type of an entry alone (`Fmt.Entry`, Fmt/Plan.lean). STATEMENTS
ALONE: one definition with code, this file's own, and three definitions of propositions. NOTHING IS
PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `sigmaBat es`      THIS FILE's OWN: the rows of every entry of es that is named "BAT-sigma" and
                     has an entry named "BAT" RIGHT BEHIND it, in their order
  `SigmaBatAppend`   joining two lists takes no such pair away: sigmaBat A ++ sigmaBat B is a
                     sublist of sigmaBat (A ++ B) (the seam can only add one)
  `SigmaBatMid`      a list pre ++ (x :: b :: post), x named "BAT-sigma", b named "BAT": [x.rows]
                     is a sublist of its sigmaBat
  `SigmaBatFamily`   a family of lists, each with [r x] a sublist of its sigmaBat: the r's, in the
                     family's order, are a sublist of sigmaBat of the joined list with anything
                     behind

WHAT IT IS FOR. In the plan of a proof's first chain the round that batches a segment's claims is
named "BAT-sigma" and stands right before the frame's "BAT". WHAT IT IS NOT. THAT IS NOT SAID HERE:
no plan, no planner and no public file is named.

NEAR. `k9Runs` (Johnson/Desc/First/Batch/Law/Condition.lean): the same marker on a written list's
records and runs. `tailCut` (Johnson/Desc/First/Driver/Cut.lean), which cuts a segment's later
rounds into named steps, refuses unless "BAT-sigma" stands right before the first "BAT".

Limits. Lists. Nothing on any property.
-/
import Fmt.Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8

/-- **The marker.** This file's own. -/
def sigmaBat : List Fmt.Entry → List Nat
  | a :: b :: t =>
    (if a.name == "BAT-sigma" && b.name == "BAT" then [a.rows] else []) ++ sigmaBat (b :: t)
  | _ => []

/-- The statement on joining. Not proved here; a lemma's statement, none of the library's goals. -/
def SigmaBatAppend : Prop :=
  ∀ A B : List Fmt.Entry, (sigmaBat A ++ sigmaBat B).Sublist (sigmaBat (A ++ B))

/-- The statement on one pair. Not proved here; a lemma's statement, none of the library's goals. -/
def SigmaBatMid : Prop :=
  ∀ (pre post : List Fmt.Entry) (x b : Fmt.Entry), x.name = "BAT-sigma" → b.name = "BAT" →
    [x.rows].Sublist (sigmaBat (pre ++ (x :: b :: post)))

/-- The statement on a family. Not proved here; a lemma's statement, none of the library's goals. -/
def SigmaBatFamily : Prop :=
  ∀ (α : Type) (f : α → List Fmt.Entry) (r : α → Nat) (l : List α),
    (∀ x ∈ l, [r x].Sublist (sigmaBat (f x))) →
    ∀ rest : List Fmt.Entry, (l.map r).Sublist (sigmaBat (l.flatMap f ++ rest))

end P1K8

#print axioms P1K8.sigmaBat
#print axioms P1K8.SigmaBatAppend
#print axioms P1K8.SigmaBatMid
#print axioms P1K8.SigmaBatFamily
