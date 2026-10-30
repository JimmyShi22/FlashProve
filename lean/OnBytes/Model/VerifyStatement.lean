-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyStatement.lean: the statement that a proof's first chain binds, compared with
what the sub-proofs use.

The statement of a proof's first chain holds the request twice: as its fourth item the request file,
whole, and as its item `request` 177 words of 32 bits
(OnBytes/Proof/RequestItem.lean; docs/format/FORMAT.md, 12.3, R15.x). Most words are numbers of the
parameter file's lines, and some are digests of tables and of call lists. RequestItem.lean forms the
words from the files' bytes. The checks of the sub-proofs work with numbers, tables and call lists
that another reader has taken from the same files (OnBytes/Model/Config.lean) or has computed. This
file compares the two, word by word. The purpose is that the chain does not bind one number while a
sub-proof uses another. What the comparison leaves out is listed below.

The C++ verifier has one statement, into which the code that uses a number also writes it, and
tests that every word was written (verifier/src/cp_verify.cpp, "internal-statement-cover"). The
comparison here takes the place of that test. It is made on an item that RequestItem.lean has
formed, so the parameter file has the lines with the tables' digests. A difference is therefore
meant to show a fault of this program and not of a file, and the refusal has an internal name. That
no file can cause one is not proved.

Main definitions: `wordsAt`, `namesHeld`, `tableWordsHeld`, `statementHeld`.
What is not claimed: no theorem is stated here.
What is not compared: the first two words (a constant and the version), the reply's word, and the
digests of the scale file and of the request, which both sides would form by the same function from
the same bytes. The numbers are compared with the scan's list of names and values. The sub-proofs
read the scan's record, which OnBytes/Model/Config.lean fills from that list.
-/
import OnBytes.Model.VerifyPublic
import OnBytes.Proof.RequestItem

namespace OnBytes.Model.Verify

/-- The n words of the item from word i on, as bytes. -/
def wordsAt (item : ByteArray) (i n : Nat) : ByteArray := item.extract (4 * i) (4 * (i + n))

/-- True if the words of the item from word `first` on are the numbers that the scan has read for
the lines whose names are listed in `names`, separated by spaces. -/
def namesHeld (P : PolScan) (item : ByteArray) (first : Nat) (names : String) : Bool :=
  (names.splitOn " ").zipIdx.all fun x => wordsAt item (first + x.2) 1 == word32 (P.value x.1)

/-- True if the eight words of the item from word `first` on are the digest that the scan has read
for a public table. `publicOf` has compared the table that the lookups read with the same
lines. -/
def tableWordsHeld (P : PolScan) (item : ByteArray) (first : Nat) (t : PublicTable) : Bool :=
  P.tableExpected t == some (wordsAt item first 8)

/-- Compares the item `request` with the public part: the numbers of the value lines, the digests of
the four tables and of the three call lists, the security target (line sec), and four numbers of the
weight table as the planner takes them. The places are those of R15.x (12.3 of the format page). -/
def statementHeld (X : Public) (item : ByteArray) : Except String Unit :=
  let d := X.digests
  let frame := X.P.frame
  if item.size == 708 &&
      namesHeld X.P item 2 Proof.names2 && wordsAt item 29 8 == d.hCalls &&
      namesHeld X.P item 37 Proof.names37 && tableWordsHeld X.P item 71 .silu &&
      tableWordsHeld X.P item 79 .sigmoid && tableWordsHeld X.P item 87 .rope &&
      namesHeld X.P item 103 Proof.names103 && tableWordsHeld X.P item 114 .exp &&
      wordsAt item 122 8 == d.hCallsA && namesHeld X.P item 130 Proof.names130 &&
      wordsAt item 155 8 == d.hCallsH && wordsAt item 172 1 == word32 X.P.hb &&
      wordsAt item 173 1 == word32 X.P.lkW && wordsAt item 174 1 == word32 frame.tableRowsLog &&
      wordsAt item 175 1 == word32 frame.tableLogN &&
      wordsAt item 176 1 == word32 frame.tableRandom then pure ()
  else throw "internal-statement-two-ways"

/-- The names with which this file refuses. -/
def namesStatement : List String := ["internal-statement-two-ways"]

end OnBytes.Model.Verify
