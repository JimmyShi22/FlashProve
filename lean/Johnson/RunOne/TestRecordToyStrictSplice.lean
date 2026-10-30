-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/TestRecordToyStrictSplice.lean: the second compiler's strict verifier of the link on
the splices of OnBytes/Entry/TestRecordToySplice.lean, and on the honest toy entry file under a
first table whose record is another.
What is run, what the stages' names and the switches (bend, lenient, noDecision) mean, and what is
not claimed: the head of Johnson/RunOne/TestRecordToyStrict.lean.
Which guards reach the compiled verifier: the first (the splices behind the lenient converter) and
the two with a record changed behind the converter. The others end at a converter or at the test
"fit" in front of the verifier.
What is expected, and why.
The three splices lay honest bytes of one stored table's opening into the copy's opening: columns of
canonical elements and salts, of the same lengths. An opening enters no query (R8.2's table). So the
lenient converter cuts the file at the same places and the chain returns; a changed leaf does not
lead to the copy's root (R7.10). Held: behind the lenient converter the first line that says no is
"after 3", the openings lead to their roots. For the verifier the three are one case, a changed leaf
under the root that the entry file brings; the line does not tell which leaf. Behind the strict
converter, which is Entry.read: "converter"; that follows from the endings that
OnBytes/Entry/TestRecordToySplice.lean holds for Entry.check.
Another record of the first table, of the right number of answers: one answer replaced by its
neighbour; two in each other's places.
  Handed to the converter. The answers stand in the statement (R13.5), which enters the chain's
  first value (R4.6): the draws move, and whether the file can then be cut depends on the bytes.
  Held: behind the strict converter "converter"; behind the lenient one, with the decision taken
  out, the run does not end in "yes". Not held: at which stage it ends.
  Changed behind the converter (bend), which has read the honest file under the honest record. The
  tests in front of the verifier pass: they read the number and the form of the answers, and the
  seeds follow from the table's name, which holds no answer (R4.10). The verifier makes the chain
  anew from the changed answers, so it draws other positions than those at which the file's trees
  are opened. Held, with the decision taken out: the fourteen lines are reached, and the first that
  says no is "strict 3", the file's own trees are opened at read leaves alone.
An answer less, and one more. Handed to a converter: both make the first table's key before they
read the chain (Entry.read: tableKey; convLax: Tie.entryPlaceR, keyWith), and that asks the shape's
number of answers: "converter". Changed behind the converter: "fit", whose test asks the same
number.
Every test is checked when the file compiles. The program verify-on-bytes does not import this file.
-/
import Johnson.RunOne.TestRecordToyStrictCopies
import OnBytes.Entry.TestRecordToySplice

set_option autoImplicit false

namespace Johnson.RunOne.RecordToyStrictSplice
open OnBytes OnBytes.Entry.RecordToy OnBytes.Entry.RecordToySplice Johnson.RunOne.RecordToyStrict

/-- The endings of the three splices. -/
def spliceEndings (lenient : Bool) : Option (List (Option String)) :=
  splices.map fun l => l.map fun s => voice lenient false s.2

/-- The ending of the honest file under the first table with its answers changed by g. -/
def underRecord (lenient noDecision : Bool) (g : List E → List E) : Option String :=
  (otherRecord g).map fun t => (endingAt id lenient noDecision t entryFile).1

/-- The honest file, read by the strict converter under the honest record; then the first table's
answers are changed by g in the converter's value. The decision is taken out. Returns the ending and
the number of named lines that were reached. -/
def bentRecord (g : List E → List E) : Option (String × Nat) :=
  firstTable.map fun t =>
    endingAt (fun a => { a with first := { a.first with answers := g a.first.answers } }) false true
      t entryFile

end Johnson.RunOne.RecordToyStrictSplice

open Johnson.RunOne.RecordToyStrictSplice Johnson.RunOne.RecordToyStrict
open OnBytes.Entry.RecordToySplice (replaced exchanged)

-- the splices
#guard spliceEndings true == some (List.replicate 3 (some "after 3"))
#guard spliceEndings false == some (List.replicate 3 (some "converter"))
-- another record of the right length, handed to the converter
#guard [underRecord false false replaced, underRecord false false exchanged] ==
  [some "converter", some "converter"]
#guard refused (underRecord true true replaced)
#guard refused (underRecord true true exchanged)
-- the same, changed behind the converter: the compiled verifier is reached and says no
#guard bentRecord replaced == some ("strict 3", 14)
#guard bentRecord exchanged == some ("strict 3", 14)
-- an answer less, one more: handed to either converter; changed behind the converter
#guard [underRecord false false (·.drop 1), underRecord true false (·.drop 1),
    underRecord false false (fun l => l ++ l.take 1),
    underRecord true false (fun l => l ++ l.take 1)] == List.replicate 4 (some "converter")
#guard [bentRecord (·.drop 1), bentRecord fun l => l ++ l.take 1] ==
  [some ("fit", 0), some ("fit", 0)]
