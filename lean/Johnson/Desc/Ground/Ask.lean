-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Ask.lean: a list of named clauses as a test with a named refusal, and the test
that every claim which lies open on a group is one that could be laid on it now.

This file holds definitions only; no theorem is stated.

Main names: refuse (as a refusal: "not met: " and the name of the first failing clause);
openClaimsE (the eight clauses of rowL, Johnson/Desc/First/Base/Ground.lean, asked of every open row
of a group; where the group is not there it refuses under "addRows: the group is not there").

What is not claimed. That these tests are the program's. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.First.Base.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params

/-- The first failing clause's name, as a refusal. A clause's name says what is asked, so the
refusal sets "not met: " in front of it. -/
def refuse (l : Clauses) : Except String Unit :=
  match l.find? (!·.2) with
  | some c => .error ("not met: " ++ c.1)
  | none => .ok ()

/-- **Every claim that lies open on the group g is one that could be laid on it now**: the eight
clauses that are asked when a claim is laid on a group (rowL). None of the eight reads the group's
open claims (they read its mark, its members, their tables and pads), so to ask them of the claims
as they lie is to ask them as if each were laid anew. -/
def openClaimsE (S : Statement) (g : Nat) : Except String Unit :=
  match S.groups[g]? with
  | none => .error "addRows: the group is not there"
  | some G => G.rows.toList.forM fun row => refuse (rowL S g row)

end VerifiableInference.Desc.Ground
