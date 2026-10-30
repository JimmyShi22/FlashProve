-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestRecordToyCompiledSplice.lean: the compiler's verifier of the link on the splices of
OnBytes/Entry/TestRecordToySplice.lean, and on the honest toy entry file under a first table whose
record is another.

How a file is judged, the stages (a) to (f), what the outcomes (reader, verifier, accepted), the two
readers and the two controls mean, and what is not claimed: the head of
OnBytes/Tie/TestRecordToyCompiled.lean.

Which guards reach the compiled verifier: those on the splices behind the lenient reader. No guard
brings another record before it: the record stands in the description under which the chain is read
(stage c), so the reader meets it first.

What is expected, and why.
The three splices lay honest bytes of one stored table's opening into the copy's opening: columns of
canonical elements and salts, of the same lengths. The strict reader checks every opening itself, so
it refuses: reader. An opening enters no query (R8.2's table), so the lenient reader, which hashes
no leaf and walks no path, cuts the file at the same places; a changed leaf does not lead to the
copy's root (R7.10): verifier. That check is one that the compiler adds to the protocol, so the
outcome stays with the decision taken out and with the whole acceptance taken out. The verifier
itself and the second control are run on each splice, the first control on the first. For the
verifier the three are one case, a changed leaf of a stored tree; its one bit does not tell which.
Another record of the first table, of the right number of answers: one answer replaced by its
neighbour; two in each other's places. The answers stand in the statement (R13.5), which enters the
chain's first value (R4.6), so the file's proof of work does not fit (R5.5; it passes by luck once
in 256): behind the strict reader: reader. Behind the lenient one the draws move, and whether the
file can then be cut depends on the bytes. Held, with the decision taken out: refused, by whichever
stage.
An answer less, and one more: stage (b) makes the first table's key (entryPlaceR, keyWith), which
asks the shape's number of answers: reader, before either reader of the chain is asked.

Every test is checked when the file compiles. The program verify-on-bytes does not import this file.
-/
import OnBytes.Tie.TestRecordToyCompiled
import OnBytes.Entry.TestRecordToySplice

set_option autoImplicit false

namespace OnBytes.Tie.RecordToyCompiledSplice
open OnBytes.Tie.RecordToyCompiled
open OnBytes.Entry.RecordToy (entryFile)
open OnBytes.Entry.RecordToySplice (splices otherRecord)

/-- The outcome at splice number i, from 0. -/
def atSplice (rd : Reader) (tk : Taken) (i : Nat) : Option Run.PQ.Who :=
  (splices.bind (·[i]?)).bind fun s => voice rd tk s.2

/-- The outcome at the honest file under the first table with its answers changed by g. -/
def underRecord (rd : Reader) (tk : Taken) (g : List E → List E) : Option Run.PQ.Who :=
  (otherRecord g).bind fun t => run rd tk t entryFile

end OnBytes.Tie.RecordToyCompiledSplice

open OnBytes.Tie.RecordToyCompiledSplice OnBytes.Tie.RecordToyCompiled Run.PQ
open OnBytes.Entry.RecordToySplice (replaced exchanged)

-- the splices behind the strict reader
#guard [0, 1, 2].map (atSplice .strict .nothing) == List.replicate 3 (some .reader)
-- behind the lenient reader: the verifier; the two controls
#guard atSplice .lenient .nothing 0 == some .verifier
#guard atSplice .lenient .nothing 1 == some .verifier
#guard atSplice .lenient .nothing 2 == some .verifier
#guard atSplice .lenient .decision 0 == some .verifier
#guard atSplice .lenient .acceptance 0 == some .verifier
#guard atSplice .lenient .acceptance 1 == some .verifier
#guard atSplice .lenient .acceptance 2 == some .verifier
-- another record of the right length
#guard [underRecord .strict .nothing replaced, underRecord .strict .nothing exchanged] ==
  [some .reader, some .reader]
#guard refused (underRecord .lenient .decision replaced)
#guard refused (underRecord .lenient .decision exchanged)
-- an answer less, one more
#guard [underRecord .strict .nothing (·.drop 1),
    underRecord .strict .nothing (fun l => l ++ l.take 1)] == [some .reader, some .reader]
