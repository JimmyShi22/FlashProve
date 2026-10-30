-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyRead.lean: the six hidden numbers of a position, as read from the cells of the
head's ledger.

Definitions only. They are stated once, for two sides: the side that goes from the field relation to
the integers, and the side that builds the honest trace. The numbers are read from bytes NR + 0 ..
20 with NR = 99, low byte first, multiplier 1; a byte is the cell + 128 (`Dv`,
Inst/Model/Head/Trace.lean).
  `hidOf`   the six together, for integer cells. The single numbers `hidC`, `hidB`, `hidU`, `hidK`,
            `hidZ`, `hidS`, over any commutative ring, are in Inst/Model/Head/Trace.lean; its margin
            and its clauses (B2) to (B4), (Z) use them.
Notation:
  `Cells K` (Inst/Model/Head/Trace.lean): the cells of the head's own matrices and of the borrowed
    x: (feature, position) ↦ number.
  `Hid` (Inst/Model/Head/PolicyDefs.lean): the six hidden numbers of a position: c, b, u, k, z, zs.
  ledger byte: one of the 120 auxiliary bytes of a position (`Dv`, Inst/Model/Head/Trace.lean; the
    head of Inst/Model/Head/Index.lean).
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.Trace
import Inst.Model.Head.PolicyDefs

set_option autoImplicit false

namespace Inst.Model.Head

/-- the six hidden numbers of integer cells -/
def hidOf (t : Cells ℤ) : Policy.Hid := ⟨hidC t, hidB t, hidU t, hidK t, hidZ t, hidS t⟩

end Inst.Model.Head
