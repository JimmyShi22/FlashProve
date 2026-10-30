-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestRecordToyCompiledLenient.lean: the compiler's verifier of the link behind the
lenient reader: altered copies of the programs' toy entry file, and the stored entry with its two
stored tables' openings exchanged. Two small definitions and tests.

The run function `run`, its outcomes and the two controls are those of
OnBytes/Tie/TestRecordToyCompiled.lean; its head says how a file is judged. Behind the lenient
reader (`Run.laxWholeX`, Run/ParseLaxX.lean) proof of work, leaves, paths and roots are left to the
compiled verifier. So a file with a bad opening reaches it.

What is checked when the file compiles (#guard).
   The copies whose held name (OnBytes/Entry/TestRecordToy.lean) is "reader-opening" are 06, 07 and
   09: one bit turned inside an opening. No byte of an opening enters the hash chain, so the drawn
   positions stay and the lenient reader cuts the file where it cuts the honest one. Each of the
   three is refused by the compiled verifier; still refused with the decision taken out; still
   refused with the protocol's whole acceptance taken out. So a check that the compiler adds to the
   protocol refuses the programs' bytes.
   The same three outcomes at `bentSwap` (Fmt/MustBeRefused/RecordToy.lean): there the openings
   under the two stored roots are exchanged. Behind the strict reader the reader refuses it.
   The other nine copies, and the honest file under a first table whose root has bit 0 turned, are
   refused, with and without the decision. Which stage refuses is not held: an altered byte that
   enters the hash chain in front of a draw of positions moves the positions, and whether the file
   can then still be cut depends on the bytes (Run/ParseLaxX.lean, part 1 of the head). Copy 08 is
   among them: it has no held name, because the programs' reader and Entry.check name different
   first checks there.
   That the two controls accept the honest file behind this reader is a test of
   OnBytes/Tie/TestRecordToyCompiled.lean: they can say yes.

What is not claimed. What part 3 of the head of OnBytes/Tie/TestRecordToyCompiled.lean lists as not
claimed holds here too. Above all: what runs is `verifyOneProtocol` of Compile/Batch at a protocol that takes
no instance, one protocol for each pair of records, and not the verifier of the link inside
`innerCompiledVerifier`; the tests are evaluations at made-up toy data and leave no theorem on a run. Nothing on
soundness, completeness or hiding.
-/
import OnBytes.Tie.TestRecordToyCompiled

set_option autoImplicit false

namespace OnBytes.Tie.RecordToyCompiled
open OnBytes.Entry.RecordToy (copies)

/-- The altered copy of a number; no bytes if there is none. -/
def copy (number : String) : ByteArray :=
  ((copies.find? (·.1 == number)).map (·.2.1)).getD ByteArray.empty

/-- The copies whose held name is not of an opening. -/
def others : List (String × ByteArray × Option String) :=
  copies.filter (·.2.2 != some "reader-opening")

end OnBytes.Tie.RecordToyCompiled

open OnBytes.Tie.RecordToyCompiled OnBytes.Entry.RecordToy Run.PQ
open Fmt.MustBeRefused.RecordToy (bentSwap)

-- the copies with a bit turned inside an opening
#guard (copies.filter (·.2.2 == some "reader-opening")).map (·.1) == ["06", "07", "09"]

#guard voice .lenient .nothing (copy "06") == some .verifier
#guard voice .lenient .decision (copy "06") == some .verifier
#guard voice .lenient .acceptance (copy "06") == some .verifier

#guard voice .lenient .nothing (copy "07") == some .verifier
#guard voice .lenient .decision (copy "07") == some .verifier
#guard voice .lenient .acceptance (copy "07") == some .verifier

#guard voice .lenient .nothing (copy "09") == some .verifier
#guard voice .lenient .decision (copy "09") == some .verifier
#guard voice .lenient .acceptance (copy "09") == some .verifier

-- the two stored tables' openings exchanged
#guard voice .strict .nothing bentSwap == some .reader
#guard voice .lenient .nothing bentSwap == some .verifier
#guard voice .lenient .decision bentSwap == some .verifier
#guard voice .lenient .acceptance bentSwap == some .verifier

-- the other copies: refused, with and without the decision
#guard others.map (·.1) == ["01", "02", "03", "04", "05", "08", "10", "11", "12"]
#guard (others.filter fun c => !refused (voice .lenient .nothing c.2.1)).map (·.1) == []
#guard (others.filter fun c => !refused (voice .lenient .decision c.2.1)).map (·.1) == []
-- the honest file under another first root: the same
#guard refused (otherFirst.bind fun t => run .lenient .nothing t entryFile)
#guard refused (otherFirst.bind fun t => run .lenient .decision t entryFile)
