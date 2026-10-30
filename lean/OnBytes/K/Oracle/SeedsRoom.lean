-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/SeedsRoom.lean: one proposition on three configuration files: at the shape of
tables of the plan that the planner returns on them, the seeds of a table's record take at most 2^31
bytes.

Why. The input of which the commitment ID is the hash holds 24 bytes for each element of the
record's seeds: answers * (cubeBits + 1) elements. The format's hash has a domain: an input of at
most 2^32 - 144 bytes. Theorems that tie the hash over the realised oracle to the direct call
(OnBytes/K/Oracle/LeavesDigests.lean [not in this library] and what stands on it) need the input
within it. 2^31 is a round number that is enough beside a key file of at most 2^28 bytes; a greater
bound would do too.

Main definition: `SeedsRoom`.

Limits: a definition of a proposition says nothing on whether it holds: that it holds at all files
is `seedsRoom` (OnBytes/K/Oracle/SeedsRoomAll.lean). It is no test of the program, and the program
makes none: it hashes directly; the proposition is the price of the tie to the realised oracle
alone. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Verify

set_option autoImplicit false

namespace OnBytes.K.Oracle

open OnBytes.Model.Verify (planned)

/-- At the shape of tables of every plan that the planner returns on these files, the record's seeds
take at most 2^31 bytes. The planner is a function: there is at most one such plan. Where the
planner refuses the files it holds for nothing. -/
def SeedsRoom (pol KL : ByteArray) (layout : Option ByteArray) : Prop :=
  ∀ p, planned pol KL layout = .ok p →
    24 * (p.chains.tableShape.answers * (p.chains.tableShape.cubeBits + 1)) ≤ 2 ^ 31

end OnBytes.K.Oracle
