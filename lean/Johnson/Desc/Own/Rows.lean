-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Rows.lean: four small tests that are asked of a row before it is laid on a group,
in the description's own text, for every block that lays rows.

  tableThere S o part
      THE TABLE IS THERE. The statement has an oracle message number o, and its shape counts at
      least one row of this part (main or mask).
  placeFits S G o part vars index
      A SUMMAND OF A ROW FITS ITS PLACE. The message o is a member of the group G; it has the table;
      vars is the number of the table's index bits; index lies below 2 ^ (that number).
  coeffsInside c
      A RUN's COEFFICIENTS LIE INSIDE THEIR VECTOR. Coefficients that are written out: always. A
      stretch (vector, start, count): start + count is at most the vector's length.
  allZero a
      ALL THREE WORDS OF AN ELEMENT ARE 0. On words below the prime this says that the element is 0;
      on other words it says less: an element whose words are the prime's is not seen as 0 here.
What is taken from the hand-written program's files: the records Statement, Group, Oracle,
OracleShape and E with their fields, the types Part and Coeffs, and functions that return numbers:
Statement.tableBits and OracleShape.rows, with what they call (rowBits, placeBits, ceilLog2,
Code.logEll). No function of these files that says yes or no is called: a walk by constants beneath
the four finds none.
That the four say just what the program's Statement.has, Blk.placeOk, Coeffs.ok and isZeroE say, at
all arguments, is proved beside, in Johnson/Desc/Own/RowsAgree.lean, which no block imports.
LIMIT: whether these tests ask enough is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- The table is there. -/
def tableThere (S : OnBytes.Statement) (o : Nat) (part : OnBytes.Part) : Bool :=
  (S.oracles[o]?).any fun x => decide (0 < x.shape.rows part)

/-- A summand of a row fits its place. -/
def placeFits (S : OnBytes.Statement) (G : OnBytes.Group) (o : Nat) (part : OnBytes.Part)
    (vars index : Nat) : Bool :=
  G.members.contains o && tableThere S o part && vars == S.tableBits o part &&
    decide (index < 2 ^ S.tableBits o part)

/-- A run's coefficients lie inside their vector. -/
def coeffsInside : OnBytes.Coeffs → Bool
  | .own _ => true
  | .stretch v start count => decide (start + count ≤ v.size)

/-- All three words of an element are 0. -/
def allZero (a : OnBytes.E) : Bool := a.c0 == 0 && a.c1 == 0 && a.c2 == 0

end VerifiableInference.Desc.Own
