-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadTables.lean: THE OUTPUT HEAD's PLACE: A TEST WITH CODE ON THE SIX CALLS' LOOKUP TABLES, THEIR ROWS
AS NUMBERS. Definitions with code; no theorem. It imports HeadNormLaw.lean alone (for the clamp): no Mathlib:
a compiled run can evaluate the test. What the test gives is stated in HeadTablesLaw.lean.

row call u: row number u of the table of call number call, as a number: A LETTER: this file names no maker of
a table and no record type.
  bitsOf call   the table of call number call has 2^(bitsOf call) rows.
  tabOf row     THE TABLE OF LEMMA 1, OFF THE ROWS THEMSELVES: row u of call 3, divided by 2^16; 1 from 2^16 on,
                where no row stands (HeadLaw.lean's TableOk asks 1 <= tab u at every u).
  rowsOk row    THE TEST: calls 0, 1: row u is u, u < 2^16 · call 2: row u is u, u < 2^8 · call 3: row u is
                u + 2^16 e with 1 <= e <= 2^F, and e = 2^F at u = 0 · call 4: call 3's rows · call 5: row u is
                u + 2^28 (the clamp of u - 2^15 to -2047 .. 2047, and 2^11).

-/
import Johnson.Desc.Kinds.HeadNormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- The table of call number call has 2^(bitsOf call) rows. -/
def bitsOf (call : Nat) : Nat := if call == 2 then 8 else 16

/-- The table of Lemma 1, off the rows of call 3. -/
def tabOf (row : Nat → Nat → Nat) (u : Nat) : Nat := if u < 2 ^ 16 then row 3 u / 2 ^ 16 else 1

/-- A row of the clamp's table, as a number. -/
def clampRow (u : Nat) : Nat := u + 2 ^ 28 * (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11).toNat

variable [Sizes]

/-- What is asked of the rows number u < 2^16. -/
def rowsOkAt (row : Nat → Nat → Nat) (u : Nat) : Bool :=
  row 0 u == u && row 1 u == u && row 3 u % 2 ^ 16 == u && decide (1 ≤ row 3 u / 2 ^ 16) &&
    decide (row 3 u / 2 ^ 16 ≤ 2 ^ F) && row 4 u == row 3 u && row 5 u == clampRow u

/-- **THE TEST.** -/
def rowsOk (row : Nat → Nat → Nat) : Bool :=
  (List.range (2 ^ 16)).all (rowsOkAt row) && ((List.range (2 ^ 8)).all fun u => row 2 u == u) &&
    row 3 0 / 2 ^ 16 == 2 ^ F

end VerifiableInference.Desc.Kinds.Head.Law
