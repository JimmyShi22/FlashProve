-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestRowCost.lean: the closeness rounds' errors where rows cost a factor.

The lines are those of blocks/frame/examples/record.f2.txt with `rowcost 2`
(OnBytes/Plan/TestVariants.lean): a combination of the rows of an interleaved word then costs the
number of rows times a line through two words, where the count rests on the assumed theorem. All
328 rounds with a closeness term do here. Where a count rests on the lemma within a third of the
distance there is no such factor: that case is not tried. The errors that are expected were taken
from the print of the C++ planning program (blocks/frame/cp_frame.cpp, `-plan request -rounds`) on
these lines, with its stand-ins for the sub-proofs: for each round its name and minus the binary
logarithm of its error, cut to hundredths. These lines have `work closeness 0 0 0`, so no work is
counted in these rounds. Each test is checked when the file compiles. The file is no part of the
program.
-/
import OnBytes.Params.Configure
import OnBytes.Plan.TestVariants

namespace OnBytes.Params.TestRowCost

/-- The 32 lines. -/
def lines : List String := Plan.TestVariants.rowcost2

/-- The planning program's stand-ins, with one made-up range check, which enters the gate and no
round. -/
def shapes : Shapes :=
  { sub := TestStandIn.standIn, layout := ⟨List.replicate 25 []⟩, identifiers := List.range 25,
    ranges := Plan.TestStandIn.standIn, rangeChecks := [⟨64, 512, 128, 129, 2 ^ 22, (11, 12)⟩] }

/-- Minus the binary logarithm of a positive number, in hundredths, rounded down: the number is
m * 2 ^ e, and 100 times the logarithm of m, rounded up, is the logarithm of m ^ 100, rounded up. -/
def hundredths (x : Binary) : Int := -100 * x.e - (clog2 (x.m ^ 100) : Int)

/-- The names of the rounds that can have a closeness term. -/
def named : List String := ["BASE lambda", "FOLD round", "LIN point", "LINK point"]

/-- Adds one to the count of a key in a list of keys with counts. -/
def count (l : List (String × Int × Nat)) (k : String × Int) : List (String × Int × Nat) :=
  if l.any fun y => y.1 == k.1 && y.2.1 == k.2 then
    l.map fun y => if y.1 == k.1 && y.2.1 == k.2 then (y.1, y.2.1, y.2.2 + 1) else y
  else l ++ [(k.1, k.2, 1)]

/-- How many rounds of each of these names have which error, over all seven chains. The error is the
whole one, with the distance from uniform of the elements that the round draws (`wholeError`). -/
def errors : Option (List (String × Int × Nat)) :=
  (readLines (TestFile.fileOf lines)).toOption.bind fun x =>
    (configure x.1 shapes Fmt.zero32 128).toOption.map fun c =>
      ((c.proof ++ c.key ++ [c.entry]).flatMap fun p =>
        (p.rounds.filter fun r => named.contains r.entry.name).map fun r =>
          (r.entry.name, hundredths (wholeError p.set (capped p.set) r))).foldl count []

/-- The same as the planning program prints it. -/
def printed : List (String × Int × Nat) :=
  [("BASE lambda", 12800, 3), ("BASE lambda", 12801, 5), ("BASE lambda", 12802, 1),
   ("FOLD round", 12800, 9), ("FOLD round", 12801, 8), ("FOLD round", 12802, 6),
   ("FOLD round", 12803, 6), ("FOLD round", 12804, 3), ("FOLD round", 12808, 24),
   ("FOLD round", 12809, 1), ("FOLD round", 12900, 9), ("FOLD round", 12901, 8),
   ("FOLD round", 12902, 6), ("FOLD round", 12903, 6), ("FOLD round", 12904, 3),
   ("FOLD round", 12908, 24), ("FOLD round", 12909, 1), ("FOLD round", 13000, 7),
   ("FOLD round", 13001, 5), ("FOLD round", 13002, 5), ("FOLD round", 13003, 6),
   ("FOLD round", 13004, 3), ("FOLD round", 13008, 24), ("FOLD round", 13009, 1),
   ("FOLD round", 13100, 6), ("FOLD round", 13101, 3), ("FOLD round", 13102, 2),
   ("FOLD round", 13103, 5), ("FOLD round", 13104, 3), ("FOLD round", 13108, 25),
   ("FOLD round", 13109, 1), ("FOLD round", 13200, 1), ("FOLD round", 13202, 2),
   ("FOLD round", 13203, 1), ("FOLD round", 13204, 1), ("FOLD round", 13208, 25),
   ("FOLD round", 13209, 1), ("FOLD round", 13302, 2), ("FOLD round", 13308, 25),
   ("FOLD round", 13309, 1), ("FOLD round", 13402, 2), ("FOLD round", 13408, 25),
   ("FOLD round", 13409, 1), ("FOLD round", 13508, 1), ("FOLD round", 13509, 1),
   ("FOLD round", 13608, 1), ("FOLD round", 13708, 2), ("FOLD round", 14662, 2),
   ("FOLD round", 14762, 2), ("FOLD round", 14862, 2), ("FOLD round", 15033, 1),
   ("FOLD round", 15066, 1), ("FOLD round", 15098, 2), ("FOLD round", 15133, 1),
   ("FOLD round", 15166, 1), ("FOLD round", 15198, 2), ("LIN point", 12925, 2),
   ("LINK point", 12825, 1)]

-- every printed line is found with its number of rounds, and there is no other
#guard errors.any fun e => e.length == printed.length && printed.all e.contains

end OnBytes.Params.TestRowCost
