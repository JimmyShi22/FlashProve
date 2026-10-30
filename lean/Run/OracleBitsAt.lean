-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OracleBitsAt.lean: `Run.oBits` (Run/OracleBits.lean) with a function O on byte strings as an
argument where that definition has the format's realised oracle.

One definition: `oBitsAt O`: the function on bit strings that O gives: O's answer at `toBytes s`, as
256 bits. Its laws are in Run/OracleBitsAtLaws.lean.

Not claimed. Nothing on any hash function; nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import Run.OracleBits

set_option autoImplicit false

namespace Run
open Rom

/-- The function on bit strings that O gives: O's answer at `toBytes s`, as 256 bits. -/
def oBitsAt (O : ByteArray → ByteArray) : Fam (rom 256) := fun _ s => bytesToDig (O (toBytes s))

end Run
