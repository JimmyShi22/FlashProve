-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TabIsEXCode.lean: A TEST WITH CODE ON PUBLIC NUMBERS: "the table of the
exponential's lookup is the library's EX (Inst/Model/Tables.lean), at each of its 2^16 rows". One
definition (with its step and its walk). It imports nothing: so that a sheet can evaluate it.

  tabIsEXB tab     one walk over the 2^16 rows, carrying the library's running value G_u (exG)
                   beside the verdict: so the walk is linear (EX u by its own text walks from 0 to
                   u). The library's numerals (2^41 · 484 · 2^32 · 2^17) are written out.

Its law: Law/TabIsEX.lean.
WHAT IT IS NOT. IT HAS RUN NOWHERE. Nothing on soundness.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- One row: the verdict so far and the running value. -/
def tabStep (tab : Nat → Nat) (p : Bool × Nat) (u : Nat) : Bool × Nat :=
  (p.1 && tab u == (p.2 + (2 ^ 17 - 1)) / 2 ^ 17, (p.2 * 484 + (2 ^ 32 - 1)) / 2 ^ 32)

/-- The walk over the first n rows. -/
def tabRun (tab : Nat → Nat) (n : Nat) : Bool × Nat :=
  (List.range n).foldl (tabStep tab) (true, 2 ^ 41)

/-- **A TEST WITH CODE ON PUBLIC NUMBERS.** 65,536 = 2^16 rows. -/
def tabIsEXB (tab : Nat → Nat) : Bool := (tabRun tab 65536).1

end VerifiableInference.Desc.Kinds.Head.Law
