-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Entry.lean: the heads of a key file and of an entry file, and the first table's root.

An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link. The programs (the C++ implementation that
comes with this Lean code) write such files. Their layout is fixed by the format page
(docs/format/FORMAT.md, which comes with the programs), rules R13.1 to R13.3. The file has
definitions that compute, with tests, and uses no
Mathlib, neither directly nor through its imports.


Sources. Written from a restatement of section 13 of the format page (rules R13.1 to R13.3) and
from the section on the file's bytes in the programs' description of the entry file. The three
rules as restated here were compared with the page (by reading, not machine-checked), but not with
the page as it ships; this file may differ from it.


1. What the file contains.
   `headKey`, `headEntry`: The first eight bytes of a key file and of an entry file: the tag CPIK or
     CPEN, then the version H821.
   keyRoot key   The first table's root, taken from a key file. The eight-byte head is compared and
     the next 32 bytes are returned. Nothing else of the key file is read.
   The copy's root stands in bytes 8 to 39 of an entry file; the bytes of the link follow.
   `WhoE`: four names for an outcome (head, reader, decision, accepted); no function of this library
   returns one.






























2. What is checked when the file compiles. Three small tests (#guard) on made-up bytes: the two
heads have eight bytes and differ; `keyRoot` returns the 32 bytes behind a key file's head, and
refuses another head and a file that is too short. No file of the programs is read here.

3. Theorems. None in this file. The split of an entry file is defined in Run/PlanQXRun.lean
(`readHead`).


4. What is not claimed.
   The key is not verified. `keyRoot` compares eight bytes and copies 32. Whether that root belongs
   to a valid key is the caller's matter; Fmt/ and Run/ have no verifier for a key file.
   No statement on soundness follows from this file. In Fmt/ and Run/ no soundness statement is made
   for the protocol of an entry file. The library has a link protocol with such statements
   (Cb/Ld/LdLink.lean); in Fmt/ and Run/ nothing connects the two.
   It is not claimed that the decision (`Fmt.M3.dec`, Fmt/M3Dec.lean) is the one that the programs
   compute. It is a reading of the programs' description of the entry file.


   The programs distinguish "yes" from "yes, with its work counted". No such distinction is made
   here.
   The decision covers no table with a record (s > 0): `sizesOK` asks s = 0.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.Rules8XFast

namespace Fmt
namespace M3

def headKey : ByteArray := ascii "CPIKH821"
def headEntry : ByteArray := ascii "CPENH821"

/-- The first table's root out of a key file: the head is tested; the key is not verified. -/
def keyRoot (key : ByteArray) : Option ByteArray :=
  if decide (40 ≤ key.size) && key.extract 0 8 == headKey then some (key.extract 8 40) else none

inductive WhoE where
  | head | reader | decision | accepted
  deriving DecidableEq, Repr

/-! ## Tests -/

#guard headKey.size == 8 && headEntry.size == 8 && headKey != headEntry
#guard keyRoot (headKey ++ zero32) == some zero32 && keyRoot (headKey ++ zero32 ++ ascii "more") == some zero32
#guard keyRoot (headEntry ++ zero32) == none && keyRoot (headKey ++ zero32.extract 0 31) == none && keyRoot ByteArray.empty == none



end M3
end Fmt
