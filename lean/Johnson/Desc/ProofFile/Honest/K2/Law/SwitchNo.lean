-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchNo.lean: the kind "the code switch" (K2): ONE SHORT NAME:
the number at which the library's written list of places (`P5J.At.ps`, Johnson/P5J/LettersAt.lean)
first bears a switch's place. One abbreviation; nothing is proved. It stands low, so that the files
on the kind's record at the library's head and the kind's exchange by kind share one name for the
term.

  `switchNo`        `P5J.At.ps.findIdx (· == p.place)`

NEAR: `switchBorders` (Honest/K2/Law/SwitchBorders.lean; not imported) maps a list of places by the
same term, written out.

Limits. Where the list bears the place nowhere the number is the list's length. Which numbers these
are at the written places is not said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- The number at which the written list of places first bears the switch's place. -/
abbrev switchNo (p : SwitchPlace) : Nat := P5J.At.ps.findIdx (· == p.place)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchNo
