-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionExp.lean: the attention sub-proof's table of exponentials, in whole numbers.

Entry u of the table is meant to be 2^S exp(-u / 2^rx), rounded to the nearest whole number. The
table ends before the first entry that rounds to 0. The C++ programs compute it in floating point
(verifier/src/vf_attention_shape.h). This file computes it with natural numbers only. A number x
between 0 and 1 is stored as the whole number x 2^256, rounded down. First exp(-1 / 2^rx) is summed
from its series. Then each entry's exponential is the product of the one before it with that number.

Main definition: expTable. The function shape of OnBytes/Model/AttentionShape.lean calls it.

What is tested. At S = 12 and rx = 8 a test (OnBytes/Model/TestAttentionShape.lean) compares the
table's digest with eight words. They were taken from the lines texp0 to texp7 of a parameter file
with these two numbers that the C++ verifier did not refuse. The C++ verifier compares these lines
with the digest of its own table. So wherever it admits a file with these eight words, the two
tables are equal at this setting, unless the hash collides. It computes its table with the
platform's floating-point library, so this can depend on the platform, and nothing here tests it.

What is not shown. The file holds no theorem. It is not proved that every entry is correctly
rounded, nor that the table equals the C++ table at any admitted pair of S and rx. Each verifier
compares a parameter file's digest lines with its own table (tableHeld, OnBytes/Model/Config.lean),
and compares nothing if the file has no such lines. So if the tables differed at some pair, this
program would admit a parameter file that the C++ verifier refuses, and the reverse. S = 12, rx = 8
and the digest lines are conditions of the standard parameter form (servedOf,
OnBytes/Model/VerifyStages.lean). On a tie the C++ source rounds to the even neighbour and this file
rounds up. After entry 0 the exact value is never a tie, since exp of a rational number other than 0
is irrational. But both programs round approximations, and nothing here shows that none of these is
a tie.
-/

namespace OnBytes.Attention

/-- The number of binary digits that are stored after the point. -/
def expDigits : Nat := 256

/-- The loop of expUnit. It adds the terms of the series of exp(-x) at x = 2^-rx. term is term
number k, times 2^expDigits, rounded down. The terms of even number are gathered in plus and those
of odd number in minus. The first argument after rx (fuel) bounds the number of steps. -/
def expSeries (rx : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, plus, minus => plus - minus
  | fuel + 1, k, term, plus, minus =>
    if term == 0 then plus - minus
    else
      let next := term / (2 ^ rx * (k + 1))
      if k % 2 == 0 then expSeries rx fuel (k + 1) next (plus + term) minus
      else expSeries rx fuel (k + 1) next plus (minus + term)

/-- An approximation of exp(-1 / 2^rx) times 2^expDigits: every term of the series is rounded down
to a whole number. From rx = 1 on a term is at most half the term before it, so the bound on the
steps lets the loop run until a term is 0. -/
def expUnit (rx : Nat) : Nat := expSeries rx (expDigits + 2) 0 (2 ^ expDigits) 0 0

/-- The loop of expTable. x approximates exp(-u / 2^rx) times 2^expDigits for the next entry u, and
q is expUnit rx. The loop ends at the first entry that rounds to 0. The first argument after q
(fuel) bounds the number of entries that are computed. acc holds the entries so far. Nothing is
returned if none of the computed entries is 0. -/
def expLoop (S q : Nat) : Nat → Nat → Array Nat → Option (Array Nat)
  | 0, _, _ => none
  | fuel + 1, x, acc =>
    let v := (x * 2 ^ S + 2 ^ (expDigits - 1)) / 2 ^ expDigits
    if v == 0 then some acc else expLoop S q fuel (x * q / 2 ^ expDigits) (acc.push v)

/-- The table of exponentials for the largest softmax weight 2^S and the step 2^-rx. Nothing is
returned if entry 2^20 + 1 is not yet 0; the C++ program refuses such a table.
OnBytes/Model/LayerTables.lean computes other exponentials, also in whole numbers, in a fixed point
of its own. -/
def expTable (S rx : Nat) : Option (Array Nat) :=
  expLoop S (expUnit rx) (2 ^ 20 + 2) (2 ^ expDigits) #[]

end OnBytes.Attention
