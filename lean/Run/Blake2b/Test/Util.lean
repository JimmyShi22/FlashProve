-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Blake2b/Test/Util.lean

Helpers of the tests in this directory: hexadecimal digits to bytes, and a test message.
Definitions only. Only the tests of this directory use them.
-/
import Run.Blake2b.Hash

namespace Run.Blake2b.Test

/-- The value of a hexadecimal digit, 0 to 9 or a to f. It is not meant for capital letters or other
characters, for which the value has no meaning; the tables of this directory have none. -/
def hexDigit (c : Char) : UInt8 := (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt8

/-- The bytes that a string of hexadecimal digits spells, two digits for each byte. A last digit
without a partner is left out. -/
def hex (s : String) : ByteArray :=
  let rec go : List Char → ByteArray → ByteArray
    | a :: b :: r, o => go r (o.push (hexDigit a * 16 + hexDigit b))
    | _, o => o
  go s.toList ByteArray.empty

/-- The test message of n bytes: byte i is i mod 251. -/
def pattern (n : Nat) : ByteArray :=
  (List.range n).foldl (fun o i => o.push (i % 251).toUInt8) (ByteArray.emptyWithCapacity n)

end Run.Blake2b.Test
