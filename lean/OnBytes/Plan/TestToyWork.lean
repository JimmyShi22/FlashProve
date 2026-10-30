-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestToyWork.lean: tests of OnBytes/Plan/ToyWork.lean. They run when this file
compiles.

The pair. For a list of plans: the bits that their weakest round reaches without its proof of work,
and that round's bits of work, as in "96.03 + 32". There is none if no round needs its work.

 1. At full size, under record.f2.txt: the pair of a key's three chains and of an entry's chain,
    against the line "work:" that the C++ planning program (blocks/frame/cp_frame.cpp) prints.
 2. Small runs: there is a pair exactly if the plan needs work, with the file's own work; one run is
    refused at more bits than its target. A toy: key and entry have a pair with the file's work.
 3. The numbers of the line on work go with the pair: there is a count exactly if there is a pair;
    the hundredths spell the pair's first number; some round is counted. At the example file the
    most work that is declared is 32 bits, as in the pair.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.ToyWork
import OnBytes.Plan.TestStandIn
import OnBytes.Plan.TestToyRuns
import OnBytes.Plan.TestToyShapes

namespace OnBytes.Plan.TestToyWork

open OnBytes.Params
open OnBytes.Params.TestExamples

/-- The pairs of the stand-in key and of an entry under a parameter file. -/
def pairsOf (l : List String) : Option (Option String × Option String) := do
  let x ← (readLines (TestFile.fileOf l)).toOption
  let k ← keySized x.1 TestStandIn.standIn
  let a ← (oneTimePlan k).toOption
  let b ← (sharedPlan k.set k.codes k.once).toOption
  let c ← (secondPlan k.set k.once).toOption
  let e ← (entrySized x.1).toOption
  let key ← (workPair k.set [a, b, c]).toOption
  let entry ← (workPair k.set [e.2.2]).toOption
  pure (key, entry)

#guard pairsOf record == some (some "96.23 + 32", some "96.23 + 32")

/-- The numbers of the line on work go with the pair of the same plans. -/
def countFits (s : Setting) (plans : List Planned) (bits : Nat := 128) : Bool :=
  match workPair s plans bits, workCount s plans bits with
  | .ok (some p), .ok (some c, hundredths) =>
    p.startsWith (Model.Stages.hundredths hundredths ++ " + ") && decide (0 < c.rounds)
  | .ok none, .ok (none, _) => true
  | _, _ => false

/-- For the stand-in key under a parameter file: whether the numbers go with the pair, and the most
bits of work that are counted. -/
def countOf (l : List String) : Option (Bool × Option Nat) := do
  let x ← (readLines (TestFile.fileOf l)).toOption
  let k ← keySized x.1 TestStandIn.standIn
  let a ← (oneTimePlan k).toOption
  let b ← (sharedPlan k.set k.codes k.once).toOption
  let c ← (secondPlan k.set k.once).toOption
  let n ← (workCount k.set [a, b, c]).toOption
  pure (countFits k.set [a, b, c], n.1.map (·.bits))

#guard countOf record == some (true, some 32)

/-- A small run's pair goes with its plan: there is one exactly if the plan needs work, and it ends
with the file's own bits of work. -/
def fits (r : Except String ToyRun) (bits : Nat) : Bool :=
  match r with
  | .error _ => false
  | .ok x =>
    match x.workPair bits with
    | .ok (some p) => x.needsWork && p.endsWith (" + " ++ toString x.work)
    | .ok none => !x.needsWork
    | .error _ => false

#guard fits (productRun TestToyRuns.product.toUTF8) 128
#guard fits (linksRun TestToyRuns.links.toUTF8) 128
#guard fits (productRun TestToyRuns.tinyProduct.toUTF8 10) 10
#guard fits (linksRun TestToyRuns.tinyLinks.toUTF8 10) 10
#guard (productRun TestToyRuns.product.toUTF8).toOption.any fun r => countFits r.plan.set [r.plan]
#guard (linksRun TestToyRuns.tinyLinks.toUTF8 10).toOption.any fun r =>
  countFits r.plan.set [r.plan] 10
-- more bits asked than the file's target
#guard (productRun TestToyRuns.tinyProduct.toUTF8 10).toOption.any fun r =>
  (r.workPair 11).toOption.isNone

/-- The toy of the tool that makes proofs. -/
def toy : Option Configured :=
  (toyForProofs (TestFile.fileOf TestToyShapes.secondFile)
    "links 3\npending 3\nmatrix 100\nidentifiers 1 2 3\n".toUTF8).toOption

-- the toy's parameter file asks for 4, 6 and 8 bits of work before positions are drawn
#guard toy.any fun c => ((keyWorkPair c).toOption.bind id).any (·.endsWith " + 8")
#guard toy.any fun c => ((entryWorkPair c).toOption.bind id).any (·.endsWith " + 8")
#guard toy.any fun c => ((wholeWorkPair c).toOption.bind id).isSome

end OnBytes.Plan.TestToyWork
